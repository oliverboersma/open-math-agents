import FormalConjectures.GreensOpenProblems.«3»
import Mathlib

/-!
# Product-free open subsets of the unit interval

Leonardo Franchi, W. T. Gowers and Fredy Yip proved the measure bound in
“Product-free subsets of (0,1)”. Their project, formalized with Aristotle
(Harmonic), proves the bound in Lean. LDJAI provided a wrapper matching
this catalogue statement in that project. Sources:

* Franchi, Gowers and Yip, mathematical proof: https://arxiv.org/abs/2607.06073
* Authors' Lean proof: https://github.com/leo-franchi/Product-free-subsets-lean/blob/85e0c5b25c3eddb39bf08b4d136a3362890ee1c4/RequestProject/Main1.lean#L227
* LDJAI, exact target: https://github.com/LDJAI/Product-free-subsets-lean/blob/a3b73d37613bb97ca3e2379f6dfaf28f94b91b02/RequestProject/Green3LeftToSolve.lean
* Catalogue discussion: https://github.com/GuillaumeBAUD-coder/open-math-agents/issues/4848

The self-contained Lean implementation here, by @Deldor14, uses dyadic
approximation, exponential coordinates and a discrete three-prefix estimate.
The discrepancy and difference-set arguments include the final cases from
Sections 4.10 and 4.11. An independent proof of the finite packing step by
@ivillar is also available in Open Math Agents:
https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/5dd86410dfb3846d43b4369a462ff2914d3d462e/proofs/Green3.green_3.R1.H2.R1.H1.lean
-/

section FoldGR1

/-
# A finite integer formulation of Green's product problem

At resolution N=2^k, retain the open cells (i/N,(i+1)/N) lying in the given set.
A product of the cells numbered i,j meets cell l exactly when
i*j < (l+1)*N and l*N < (i+1)*(j+1). The forward implication uses the integer
endpoints. For the converse, interpolate between both endpoint products.
The finite problem does not mention real numbers or measures.

Green's problem was solved by Franchi, Gowers and Yip, arXiv:2607.06073.
This discretization and Lean proof are by @Deldor14.
-/

namespace OMA.R_Green3_green_3_R1

open Set MeasureTheory Finset

private lemma product_cells {i j l N : ℕ} (hN : 0<N)
    (hlo : i*j < (l+1)*N) (hhi : l*N < (i+1)*(j+1)) :
    ∃ x ∈ Set.Ioo ((i:ℝ)/N) (((i:ℝ)+1)/N), ∃ y ∈ Set.Ioo ((j:ℝ)/N) (((j:ℝ)+1)/N), x*y ∈ Set.Ioo ((l:ℝ)/N) (((l:ℝ)+1)/N) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hi : (0:ℝ) ≤ i := by positivity
  have hj : (0:ℝ) ≤ j := by positivity
  have hl : (i:ℝ)*j < ((l:ℝ)+1)*N := by exact_mod_cast hlo
  have hh : (l:ℝ)*N < ((i:ℝ)+1)*(j+1) := by exact_mod_cast hhi
  have hself : (i:ℝ)*j < ((i:ℝ)+1)*(j+1) := by nlinarith
  have hcross : (l:ℝ)*N < ((l:ℝ)+1)*N := by linarith
  obtain ⟨w,hw₁,hw₂⟩ := exists_between
    (max_lt (lt_min hself hl) (lt_min hh hcross))
  have hwi := (max_lt_iff.mp hw₁).1
  have hwl := (max_lt_iff.mp hw₁).2
  have hwj := (lt_min_iff.mp hw₂).1
  have hwr := (lt_min_iff.mp hw₂).2
  let f : ℝ → ℝ := fun t => ((i:ℝ)+t)*((j:ℝ)+t)
  have hc : Continuous f := by fun_prop
  have hwf : w ∈ Set.Icc (f 0) (f 1) := by simpa [f] using And.intro hwi.le hwj.le
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hc.continuousOn hwf
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by rintro rfl; simp [f] at he; linarith)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by rintro rfl; simp [f] at he; linarith)
  refine ⟨((i:ℝ)+t)/N,⟨(div_lt_div_iff_of_pos_right hNr).2 (by linarith),
    (div_lt_div_iff_of_pos_right hNr).2 (by linarith)⟩, ((j:ℝ)+t)/N,
    ⟨(div_lt_div_iff_of_pos_right hNr).2 (by linarith),
    (div_lt_div_iff_of_pos_right hNr).2 (by linarith)⟩,?_⟩
  rw [div_mul_div_comm, show ((i:ℝ)+t)*((j:ℝ)+t) = w from he]
  constructor
  · apply (div_lt_div_iff₀ hNr (mul_pos hNr hNr)).mpr
    nlinarith only [mul_lt_mul_of_pos_right hwl hNr]
  · apply (div_lt_div_iff₀ (mul_pos hNr hNr) hNr).mpr
    nlinarith only [mul_lt_mul_of_pos_right hwr hNr]

/-- Inner approximation by dyadic cells at one common resolution. -/
def H1 : Prop := ∀ A : Set ℝ, IsOpen A → A ⊆ Set.Icc 0 1 → 1/3 < volume A →
    ∃ k : ℕ, ∃ S : Finset ℕ, S ⊆ range (2^k) ∧ 2^k < 3*S.card ∧
      ∀ i ∈ S, Set.Ioo ((i:ℝ)/((2^k:ℕ):ℝ)) (((i:ℝ)+1)/((2^k:ℕ):ℝ)) ⊆ A

/-- A finite extremal problem on the integer cell indices. -/
def H2 : Prop := ∀ k : ℕ, ∀ S : Finset ℕ, S ⊆ range (2^k) → 2^k < 3*S.card →
    ∃ i ∈ S, ∃ j ∈ S, ∃ l ∈ S, i*j < (l+1)*2^k ∧ l*2^k < (i+1)*(j+1)

theorem main : H1 → H2 → type_of% @Green3.green_3 := by
  intro approx finiteCover A hA hsub hvol
  obtain ⟨k,S,hS,hcard,hcell⟩ := approx A hA hsub hvol
  obtain ⟨i,hi,j,hj,l,hl,hle,hgt⟩ := finiteCover k S hS hcard
  obtain ⟨x,hx,y,hy,hxy⟩ := product_cells (by positivity) hle hgt
  exact ⟨x,y,x*y,hcell i hi hx,hcell j hj hy,hcell l hl hxy,rfl⟩


/-- The continuous theorem also implies the finite integer statement, so the
discretization retains exactly the original extremal problem. -/
theorem finite_of_green (h : type_of% @Green3.green_3) : H2 := by
  classical
  intro k S hS hcard
  let N : ℕ := 2^k
  have hNr : (0:ℝ) < N := by dsimp [N]; positivity
  let I := fun i : ℕ => Set.Ioo ((i:ℝ)/N) (((i:ℝ)+1)/N)
  let U := ⋃ i ∈ S, I i
  have hopen : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo
  have hsub : U ⊆ Set.Icc 0 1 := by
    rintro x hx
    obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    have hiN : i+1 ≤ N := Nat.succ_le_of_lt (mem_range.mp (hS hi))
    have hri : (i:ℝ)+1 ≤ N := by exact_mod_cast hiN
    have hlo : 0 ≤ (i:ℝ)/N := by positivity
    exact ⟨hlo.trans hx.1.le,hx.2.le.trans ((div_le_one hNr).mpr hri)⟩
  have hd : (S : Set ℕ).PairwiseDisjoint I := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hle : (i:ℝ)+1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hlt)
      exact (not_lt_of_ge (div_le_div_of_nonneg_right hle hNr.le)) (hy.1.trans hx.2)
    · have hle : (j:ℝ)+1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt hlt)
      exact (not_lt_of_ge (div_le_div_of_nonneg_right hle hNr.le)) (hx.1.trans hy.2)
  have hmeas (i : ℕ) : volume (I i) = ENNReal.ofReal (1/(N:ℝ)) := by
    dsimp only [I]
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hvol : volume U = ENNReal.ofReal ((S.card:ℝ)/N) := calc
    volume U = ∑ i ∈ S, volume (I i) := measure_biUnion_finset hd (fun _ _ => measurableSet_Ioo)
    _ = ∑ _i ∈ S, ENNReal.ofReal (1/(N:ℝ)) := sum_congr rfl fun i _ => hmeas i
    _ = ENNReal.ofReal (∑ _i ∈ S, 1/(N:ℝ)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ = ENNReal.ofReal ((S.card:ℝ)/N) := by simp [nsmul_eq_mul,div_eq_mul_inv]
  have hNcard : (N:ℝ) < 3*S.card := by exact_mod_cast hcard
  have hreal : (1:ℝ)/3 < S.card/N := (lt_div_iff₀ hNr).mpr (by linarith)
  have hlarge : 1/3 < volume U := by
    rw [hvol]
    have hh := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mpr hreal
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)] at hh
    simpa using hh
  obtain ⟨x,y,z,hx,hy,hz,rfl⟩ := h U hopen hsub hlarge
  obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨j,hj,hy⟩ := mem_iUnion₂.mp hy
  obtain ⟨l,hl,hz⟩ := mem_iUnion₂.mp hz
  have hx0 : 0<x := lt_of_le_of_lt (by positivity : 0 ≤ (i:ℝ)/N) hx.1
  have hlow : ((i:ℝ)/N)*(j/N) < ((l:ℝ)+1)/N :=
    ((mul_le_mul_of_nonneg_right hx.1.le (by positivity)).trans_lt
      (mul_lt_mul_of_pos_left hy.1 hx0)).trans hz.2
  have hhigh : (l:ℝ)/N < (((i:ℝ)+1)/N)*(((j:ℝ)+1)/N) :=
    hz.1.trans ((mul_lt_mul_of_pos_left hy.2 hx0).trans
      (mul_lt_mul_of_pos_right hx.2 (by positivity)))
  rw [div_mul_div_comm,div_lt_div_iff₀ (mul_pos hNr hNr) hNr] at hlow
  rw [div_mul_div_comm,div_lt_div_iff₀ hNr (mul_pos hNr hNr)] at hhigh
  have hL : (i:ℝ)*j*N < (((l:ℝ)+1)*N)*N := by linarith only [hlow]
  have hR : (l:ℝ)*N*N < (((i:ℝ)+1)*(j+1))*N := by linarith only [hhigh]
  refine ⟨i,hi,j,hj,l,hl,?_,?_⟩
  · exact_mod_cast (lt_of_mul_lt_mul_right hL hNr.le)
  · exact_mod_cast (lt_of_mul_lt_mul_right hR hNr.le)

end OMA.R_Green3_green_3_R1

end FoldGR1

namespace GreenAssembly.GR1H1

/- Dyadic inner approximation for the finite formulation of Green 3.
Lean proof by @Deldor14. -/

open Set MeasureTheory Finset

open OMA.R_Green3_green_3_R1

theorem result : OMA.R_Green3_green_3_R1.H1 := by
  classical
  intro A hA hsub hvol
  obtain ⟨K,hKA,hK,hlarge⟩ := hA.measurableSet.exists_lt_isCompact hvol
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_thickening_subset_open hA hKA
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (1/δ) (by norm_num : (1:ℝ)<2)
  let N : ℕ := 2^k
  have hNr : (0:ℝ)<N := by dsimp [N]; positivity
  have hwidth : 1/(N:ℝ) < δ := by
    have hh : (1:ℝ)/δ < N := by simpa [N] using hk
    apply (div_lt_iff₀ hNr).2
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hh
  let C : ℕ → Set ℝ := fun i => Set.Icc ((i:ℝ)/N) (((i:ℝ)+1)/N)
  let S := (range N).filter fun i => C i ⊆ A
  have hS : S ⊆ range N := filter_subset _ _
  have hclosed (i : ℕ) (hi : i ∈ S) : C i ⊆ A := (mem_filter.mp hi).2
  have hpart : A ⊆ Set.Ioo 0 1 := by simpa using interior_maximal hsub hA
  have hcover : K ⊆ ⋃ i ∈ S, C i := by
    intro x hx
    obtain ⟨hx0,hx1⟩ := hpart (hKA hx)
    let i := ⌊x*N⌋₊
    have hfl : (i:ℝ) ≤ x*N := Nat.floor_le (by positivity)
    have hfr : x*N < (i:ℝ)+1 := Nat.lt_floor_add_one _
    have hi : (i:ℝ)<N := hfl.trans_lt (by nlinarith only [mul_lt_mul_of_pos_right hx1 hNr])
    have hir : i < N := by exact_mod_cast hi
    have hleft : (i:ℝ)/N ≤ x := (div_le_iff₀ hNr).2 hfl
    have hright : x < ((i:ℝ)+1)/N := (lt_div_iff₀ hNr).2 hfr
    have hstay : C i ⊆ A := by
      intro y hy
      apply hthick
      apply Metric.mem_thickening_iff.mpr
      refine ⟨x,hx,?_⟩
      have he : ((i:ℝ)+1)/N = (i:ℝ)/N + 1/N := add_div _ _ _
      obtain ⟨hyl,hyr⟩ := hy
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact mem_iUnion₂.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr hir,hstay⟩,hleft,hright.le⟩
  have hmeas (i : ℕ) : volume (C i) = ENNReal.ofReal (1/(N:ℝ)) := by
    rw [show C i = Set.Icc ((i:ℝ)/N) (((i:ℝ)+1)/N) from rfl, Real.volume_Icc]
    congr 1
    ring
  have hupper : volume K ≤ ENNReal.ofReal ((S.card:ℝ)/N) := calc
    volume K ≤ volume (⋃ i ∈ S, C i) := measure_mono hcover
    _ ≤ ∑ i ∈ S, volume (C i) := measure_biUnion_finset_le _ _
    _ = ∑ _i ∈ S, ENNReal.ofReal (1/(N:ℝ)) := sum_congr rfl fun i _ => hmeas i
    _ = ENNReal.ofReal (∑ _i ∈ S, 1/(N:ℝ)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ = ENNReal.ofReal ((S.card:ℝ)/N) := by simp [nsmul_eq_mul, div_eq_mul_inv]
  have hreal : (1:ℝ)/3 < S.card/N := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
    simpa using hlarge.trans_le hupper
  have hbig : (N:ℝ) < 3*S.card := by
    have h := (lt_div_iff₀ hNr).mp hreal
    linarith
  exact ⟨k,S,hS,by exact_mod_cast hbig,fun i hi => Set.Ioo_subset_Icc_self.trans (hclosed i hi)⟩

end GreenAssembly.GR1H1

section FoldGR1H2R1

/-
# Packing at the two extreme cell indices

Suppose S has first index m and last index M−1, in a grid of N cells.
On the finer integer grid, the blocks of length N above S are disjoint from
the blocks of length M above S whenever the required product triple is absent.
Both families fit between mM and MN, giving (N+M)|S| ≤ M(N−m).
Only the range N²+3mM < 2MN can therefore support a counterexample of density
above one third. Lean proof by @Deldor14.
-/

namespace OMA.R_Green3_green_3_R1_H2_R1

open Finset

/-- Counting the integer blocks from the largest occupied cell. -/
def H1 : Prop := ∀ (N m M : ℕ) (S : Finset ℕ), 0 < M → M ≤ N →
    M-1 ∈ S → (∀ i ∈ S, m ≤ i ∧ i < M) →
    (∀ i ∈ S, ∀ j ∈ S, ∀ l ∈ S, ¬(i*j < (l+1)*N ∧ l*N < (i+1)*(j+1))) →
    (N+M)*S.card ≤ M*(N-m)

/-- The remaining integer configurations after accounting for both occupied extremes. -/
def H2 : Prop := ∀ (k m M : ℕ) (S : Finset ℕ), 0 < M → M ≤ 2^k →
    m ∈ S → M-1 ∈ S → (∀ i ∈ S, m ≤ i ∧ i < M) →
    (2^k)^2 + 3*m*M < 2*M*(2^k) → 2^k < 3*S.card →
    ∃ i ∈ S, ∃ j ∈ S, ∃ l ∈ S, i*j < (l+1)*2^k ∧ l*2^k < (i+1)*(j+1)

theorem main : H1 → H2 → OMA.R_Green3_green_3_R1.H2 := by
  classical
  intro pack tail k S hr hc
  let N := 2^k
  have hn : 0 < N := by dsimp [N]; positivity
  have hcard : N < 3*S.card := hc
  have hne : S.Nonempty := card_pos.mp (by omega)
  let m := S.min' hne
  let M := S.max' hne+1
  have hm := S.min'_mem hne
  have hM := S.max'_mem hne
  have hpM : 0 < M := Nat.zero_lt_succ _
  have hMN : M ≤ N := Nat.succ_le_of_lt (mem_range.mp (hr hM))
  have hMm : M-1 ∈ S := by simpa [M] using hM
  have hbounds (i : ℕ) (hi : i ∈ S) : m ≤ i ∧ i < M :=
    ⟨S.min'_le i hi,Nat.lt_succ_of_le (S.le_max' i hi)⟩
  by_contra! hno
  have absent : ∀ i ∈ S, ∀ j ∈ S, ∀ l ∈ S, ¬(i*j < (l+1)*N ∧ l*N < (i+1)*(j+1)) := by
    intro i hi j hj l hl h
    exact (not_lt_of_ge (hno i hi j hj l hl h.1)) h.2
  have hbound := pack N m M S hpM hMN hMm hbounds absent
  have hmN : m ≤ N := (hbounds m hm).2.le.trans hMN
  have hsplit : N-m+m = N := Nat.sub_add_cancel hmN
  have hres : N^2 + 3*m*M < 2*M*N := by
    nlinarith only [Nat.mul_lt_mul_of_pos_left hcard (by omega : 0<N+M),
      Nat.mul_le_mul_left 3 hbound, congrArg (fun t : ℕ => 3*M*t) hsplit]
  obtain ⟨i,hi,j,hj,l,hl,hi',hj'⟩ := tail k m M S hpM hMN hm hMm hbounds hres hc
  exact absent i hi j hj l hl ⟨hi',hj'⟩

end OMA.R_Green3_green_3_R1_H2_R1

end FoldGR1H2R1

namespace GreenAssembly.GR1H2R1H1

/- The two disjoint integer packings associated to the largest occupied cell.
One uses blocks of the original grid width and the other uses a scaled copy.
Lean proof by @Deldor14. -/

open Finset

private lemma block_step {i j t r : ℕ} (hr : r<t) (hij : i<j) : i*t+r < j*t := calc
  _ < (i+1)*t := by nlinarith
  _ ≤ j*t := Nat.mul_le_mul_right _ hij

theorem result : OMA.R_Green3_green_3_R1_H2_R1.H1 := by
  intro N m M S hpM hMN hM hrange hno
  let B (t : ℕ) := (S ×ˢ range t).image (fun x => x.1*t+x.2)
  have hcard (t : ℕ) : (B t).card = S.card*t := by
    dsimp [B]
    rw [card_image_of_injOn]
    · simp
    · intro ⟨i,r⟩ hi ⟨j,u⟩ hj he
      have hr := mem_range.mp (mem_product.mp hi).2
      have hu := mem_range.mp (mem_product.mp hj).2
      change i*t+r = j*t+u at he
      rcases lt_trichotomy i j with hij | rfl | hji
      · have hh := block_step hr hij
        omega
      · have hru : r=u := by omega
        simp [hru]
      · have hh := block_step hu hji
        omega
  have hb {t z : ℕ} (hz : z ∈ B t) : ∃ i ∈ S, i*t ≤ z ∧ z < (i+1)*t := by
    obtain ⟨⟨i,r⟩,hi,rfl⟩ := mem_image.mp hz
    have hr := mem_range.mp (mem_product.mp hi).2
    exact ⟨i,(mem_product.mp hi).1,Nat.le_add_right ..,block_step hr (Nat.lt_succ_self i)⟩
  have hd : Disjoint (B N) (B M) := by
    apply disjoint_left.mpr
    intro z hzN hzM
    obtain ⟨l,hl,hl₁,hl₂⟩ := hb hzN
    obtain ⟨j,hj,hj₁,hj₂⟩ := hb hzM
    have hle : (M-1)*j ≤ j*M := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.sub_le ..)
    apply hno (M-1) hM j hj l hl
    refine ⟨(hle.trans hj₁).trans_lt hl₂,?_⟩
    rw [Nat.sub_add_cancel hpM,Nat.mul_comm M (j+1)]
    exact hl₁.trans_lt hj₂
  have hsub : B N ∪ B M ⊆ Ico (m*M) (M*N) := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨i,hi,hlo,hhi⟩ := hb hz
      obtain ⟨hl,hh⟩ := hrange i hi
      exact mem_Ico.mpr ⟨(Nat.mul_le_mul hl hMN).trans hlo,
        hhi.trans_le (Nat.mul_le_mul_right _ hh)⟩
    · obtain ⟨i,hi,hlo,hhi⟩ := hb hz
      obtain ⟨hl,hh⟩ := hrange i hi
      exact mem_Ico.mpr ⟨(Nat.mul_le_mul_right _ hl).trans hlo,
        hhi.trans_le (Nat.mul_le_mul hh hMN)⟩
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hd,hcard,hcard,Nat.card_Ico] at hcount
  calc
    (N+M)*S.card = S.card*N+S.card*M := by ring
    _ ≤ M*N-m*M := hcount
    _ = M*(N-m) := by rw [Nat.mul_sub, Nat.mul_comm m M]

end GreenAssembly.GR1H2R1H1

section FoldGR1H2R1H2R1

/-
# Green's product problem on a geometric grid

For the cells [q^(j+1), q^j], products correspond to addition of
exponents.  The finite counterpart of the three-prefix inequality in
Franchi, Gowers and Yip, "Product-free subsets of (0,1)", Lemma 2.1
(arXiv:2607.06073), suffices. The proof only needs its strict version at
thresholds u+a at which both outer windows are about to gain one point.
The matching argument for the generating polynomial is discrete.
Original Lean formalization by @Deldor14.
-/

namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1

open MeasureTheory Finset

private lemma low_prefix (T : Finset ℕ) (a : ℕ) (ha : a ∈ T) (hmin : ∀ i ∈ T, a ≤ i)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (n : ℕ) (hn : n ≤ 2*a) :
    (T.filter (· < n-a)).card + (T.filter (· < n)).card + (T.filter (· < n+a)).card ≤ n := by
  classical
  have he : T.filter (· < n-a) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hi,hil⟩ := mem_filter.mp hi
    have hai := hmin i hi
    omega
  rw [he,card_empty,zero_add]
  let L := (T.filter (· < n)).image (· + a)
  let R := T.filter (· < n+a)
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro i hi hr
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hi
    have h := hsep z (mem_filter.mp hz).1 a ha (z+a) (mem_filter.mp hr).1
    omega
  have hsub : L ∪ R ⊆ Ico a (n+a) := by
    intro i hi
    rcases mem_union.mp hi with hl | hr
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hl
      have hzn := (mem_filter.mp hz).2
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨hi,hin⟩ := mem_filter.mp hr
      exact mem_Ico.mpr ⟨hmin i hi,hin⟩
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis,Nat.card_Ico] at hc
  simpa [L,R,card_image_of_injective _ (add_left_injective a)] using hc

private lemma high_prefix (T : Finset ℕ) (a n : ℕ) (hn : 3*T.card ≤ n) :
    (T.filter (· < n-a)).card + (T.filter (· < n)).card + (T.filter (· < n+a)).card ≤ n := by
  have h (m : ℕ) := Finset.card_filter_le T (· < m)
  have h₁ := h (n-a)
  have h₂ := h n
  have h₃ := h (n+a)
  omega

private lemma count_next (T : Finset ℕ) (m : ℕ) :
    (T.filter (· < m+1)).card = (T.filter (· < m)).card + if m ∈ T then 1 else 0 := by
  by_cases h : m ∈ T
  · have he : T.filter (· < m+1) = insert m (T.filter (· < m)) := by
      ext i
      simp only [mem_filter,mem_insert]
      constructor
      · rintro ⟨hi,hlt⟩
        by_cases h' : i=m
        · exact Or.inl h'
        · exact Or.inr ⟨hi,by omega⟩
      · rintro (rfl | ⟨hi,hle⟩)
        · exact ⟨h,by omega⟩
        · exact ⟨hi,by omega⟩
    rw [he]
    simp [h]
  · have he : T.filter (· < m+1) = T.filter (· < m) := by
      ext i
      simp only [mem_filter]
      constructor
      · rintro ⟨hi,hle⟩
        have hne : i ≠ m := by rintro rfl; exact h hi
        exact ⟨hi,by omega⟩
      · rintro ⟨hi,hle⟩
        exact ⟨hi,by omega⟩
    rw [he]
    simp [h]

private lemma cumulative_of_double_hits (T : Finset ℕ) (a : ℕ) (ha : a ∈ T)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (low : ∀ n ≤ 2*a, (T.filter (· < n-a)).card + (T.filter (· < n)).card +
      (T.filter (· < n+a)).card ≤ n)
    (high : ∀ n, 3*T.card ≤ n → (T.filter (· < n-a)).card + (T.filter (· < n)).card +
      (T.filter (· < n+a)).card ≤ n)
    (core : ∀ u ∈ T, u+2*a ∈ T → u+a+1 < 3*T.card →
      (T.filter (· < u)).card + (T.filter (· < u+a)).card + (T.filter (· < u+2*a)).card < u+a)
    (n : ℕ) :
    (T.filter (· < n-a)).card + (T.filter (· < n)).card + (T.filter (· < n+a)).card ≤ n := by
  induction n with
  | zero => exact low 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases hlow : n+1 ≤ 2*a
    · exact low _ hlow
    by_cases hhigh : 3*T.card ≤ n+1
    · exact high _ hhigh
    have hma : a ≤ n := by omega
    obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hma
    have hf {z : ℕ} (hz : z ∈ T) : z+a ∉ T := by
      intro h
      have hh := hsep z hz a ha (z+a) h
      omega
    have e₁ : a+u+1-a = u+1 := by omega
    have e₂ : a+u+1 = (u+a)+1 := by omega
    have e₃ : a+u+1+a = (u+2*a)+1 := by omega
    have e₄ : a+u-a = u := by omega
    have e₅ : a+u = u+a := by omega
    have e₆ : a+u+a = u+2*a := by omega
    change (T.filter (· < a+u+1-a)).card + (T.filter (· < a+u+1)).card +
      (T.filter (· < a+u+1+a)).card ≤ a+u+1
    rw [e₁,e₃,e₂,count_next,count_next,count_next]
    rw [e₄,e₆,e₅] at ih
    by_cases hm : u+a ∈ T
    · have hl : u ∉ T := fun h => hf h hm
      have hr : u+2*a ∉ T := by simpa [two_mul,add_assoc] using hf hm
      simp only [hm,hl,hr,if_true,if_false] 
      omega
    · by_cases hl : u ∈ T
      · by_cases hr : u+2*a ∈ T
        · have hsave := core u hl hr (by omega)
          simp only [hm,hl,hr,if_true,if_false]
          omega
        · simp only [hm,hl,hr,if_true,if_false]
          omega
      · simp only [hm,hl,if_false]
        split <;> omega

/-- A geometric mesh extracts a finite set of sum-free closed exponent intervals. -/
def H1 : Prop := ∀ U : Set ℝ, IsOpen U → U ⊆ Set.Icc 0 1 → 1/3 < volume U →
    (∀ x ∈ U, ∀ y ∈ U, x*y ∉ U) →
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ T : Finset ℕ, T.Nonempty ∧
      (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) ∧
      1/3 < (1-q)*(∑ i ∈ T, q^i)

/-- At a simultaneous hit in the outer two windows there is one spare position.
This discrete statement follows mathematically from Lemma 2.1 of Franchi,
Gowers and Yip, applied to the union of the closed intervals [j,j+1]. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a : ℕ), a ∈ T → (∀ i ∈ T, a ≤ i) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    ∀ u ∈ T, u+2*a ∈ T → u+a+1 < 3*T.card →
      (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

/-- A bound on three shifted prefix counts bounds the generating polynomial. -/
def H3 : Prop := ∀ (T : Finset ℕ) (a : ℕ), (∀ i ∈ T, a ≤ i) →
    (∀ n : ℕ, (T.filter (· < n-a)).card + (T.filter (· < n)).card +
      (T.filter (· < n+a)).card ≤ n) →
    ∀ q : ℝ, 0 < q → q < 1 → (1-q)*(∑ i ∈ T, q^i) ≤ 1/3

theorem main : H1 → H2 → H3 → OMA.R_Green3_green_3_R1_H2_R1.H2 := by
  classical
  intro geometric critical weights k m M S _hpos htop _hmin _hmax bounds _hcase hdense
  have hg : type_of% @Green3.green_3 := by
    intro U hU hu hvol
    by_contra h
    have habsent : ∀ x ∈ U, ∀ y ∈ U, x*y ∉ U :=
      fun x hx y hy hxy => h ⟨x,y,x*y,hx,hy,hxy,rfl⟩
    obtain ⟨q,hq,hq1,T,hT,hsep,hbig⟩ := geometric U hU hu hvol habsent
    let a := T.min' hT
    have ha : a ∈ T := T.min'_mem hT
    have hmin (i : ℕ) (hi : i ∈ T) : a ≤ i := T.min'_le i hi
    have hcum := cumulative_of_double_hits T a ha hsep (low_prefix T a ha hmin hsep)
      (high_prefix T a) (critical T a ha hmin hsep)
    exact (not_lt_of_ge (weights T a hmin hcum q hq hq1)) hbig
  exact OMA.R_Green3_green_3_R1.finite_of_green hg k S
    (fun i hi => mem_range.mpr ((bounds i hi).2.trans_le htop)) hdense

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1

end FoldGR1H2R1H2R1

namespace GreenAssembly.GR1H2R1H2R1H1

/- Inner approximation by closed geometric cells. Original Lean proof by @Deldor14.
The three-prefix inequality is from Franchi–Gowers–Yip, arXiv:2607.06073, Lemma 2.1. -/

open Set MeasureTheory Finset

private lemma bracket (q : ℝ) (B : ℕ) (x : ℝ) (hx : q^B ≤ x) (hx1 : x < 1) :
    ∃ i < B, q^(i+1) ≤ x ∧ x ≤ q^i := by
  induction B with
  | zero => simp at hx; linarith
  | succ B ih =>
    by_cases h : q^B ≤ x
    · obtain ⟨i,hi,hil,hir⟩ := ih h
      exact ⟨i,by omega,hil,hir⟩
    · exact ⟨B,by omega,hx,(not_le.mp h).le⟩

private lemma geometric_extraction (U : Set ℝ) (hU : IsOpen U) (hu : U ⊆ Icc 0 1)
    (hvol : 1/3 < volume U) (hp : ∀ x ∈ U, ∀ y ∈ U, x*y ∉ U) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ T : Finset ℕ, T.Nonempty ∧
      (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) ∧
      1/3 < (1-q)*(∑ i ∈ T, q^i) := by
  classical
  obtain ⟨K,hKU,hK,hlarge⟩ := hU.measurableSet.exists_lt_isCompact hvol
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_thickening_subset_open hU hKU
  let q := 1 - min (δ/2) (1/2)
  have hw : 0 < min (δ/2) (1/2:ℝ) := lt_min (by positivity) (by norm_num)
  have hq : 0 < q := by dsimp [q]; linarith [min_le_right (δ/2) (1/2:ℝ)]
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hδq : 1-q < δ := by dsimp [q]; linarith [min_le_left (δ/2) (1/2:ℝ)]
  have hpart : U ⊆ Set.Ioo 0 1 := by simpa using interior_maximal hu hU
  have hne : K.Nonempty := by
    by_contra! h
    simp [h] at hlarge
  obtain ⟨x₀,hx₀,hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨B,hB⟩ := exists_pow_lt_of_lt_one (hpart (hKU hx₀)).1 hq1
  let C : ℕ → Set ℝ := fun i => Icc (q^(i+1)) (q^i)
  let T := (range B).filter (fun i => C i ⊆ U)
  have hclosed (i : ℕ) (hi : i ∈ T) : C i ⊆ U := (mem_filter.mp hi).2
  have hend (i : ℕ) : q^(i+1) ≤ q^i := pow_le_pow_of_le_one hq.le hq1.le (by omega)
  have hcover : K ⊆ ⋃ i ∈ T, C i := by
    intro x hx
    obtain ⟨i,hi,hil,hir⟩ := bracket q B x (hB.le.trans (hmin hx)) (hpart (hKU hx)).2
    have hsmall : q^i-q^(i+1) < δ := calc
      _ = (1-q)*q^i := by rw [pow_succ]; ring
      _ ≤ (1-q)*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hq.le hq1.le) (by linarith)
      _ < δ := by simpa using hδq
    have hstay : C i ⊆ U := by
      intro y hy
      apply hthick
      apply Metric.mem_thickening_iff.mpr
      refine ⟨x,hx,?_⟩
      obtain ⟨hyl,hyr⟩ := hy
      rw [Real.dist_eq,abs_lt]
      constructor <;> linarith
    exact mem_iUnion₂.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr hi,hstay⟩,hil,hir⟩
  have hmeas (i : ℕ) : volume (C i) = ENNReal.ofReal ((1-q)*q^i) := by
    rw [show C i = Icc (q^(i+1)) (q^i) from rfl,Real.volume_Icc,pow_succ]
    congr 1
    ring
  have hupper : volume K ≤ ENNReal.ofReal ((1-q)*(∑ i ∈ T, q^i)) := calc
    volume K ≤ volume (⋃ i ∈ T, C i) := measure_mono hcover
    _ ≤ ∑ i ∈ T, volume (C i) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ T, ENNReal.ofReal ((1-q)*q^i) := sum_congr rfl fun i _ => hmeas i
    _ = ENNReal.ofReal (∑ i ∈ T, (1-q)*q^i) := (ENNReal.ofReal_sum_of_nonneg
          (fun i _ => mul_nonneg (sub_nonneg.mpr hq1.le) (pow_nonneg hq.le i))).symm
    _ = _ := by rw [Finset.mul_sum]
  have hbig : (1:ℝ)/3 < (1-q)*(∑ i ∈ T, q^i) := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
    simpa using hlarge.trans_le hupper
  have hT : T.Nonempty := by
    by_contra! h
    simp [h] at hbig
    linarith
  have upper (i : ℕ) (hi : i ∈ T) : q^i ∈ U := hclosed i hi ⟨hend i,le_rfl⟩
  have lower (i : ℕ) (hi : i ∈ T) : q^(i+1) ∈ U := hclosed i hi ⟨le_rfl,hend i⟩
  refine ⟨q,hq,hq1,T,hT,?_,hbig⟩
  intro i hi j hj l hl
  by_contra! hf
  have hcases : l+1=i+j ∨ l=i+j ∨ l=(i+1)+j ∨ l=(i+1)+(j+1) := by omega
  rcases hcases with h | h | h | h
  · exact hp _ (upper i hi) _ (upper j hj) (by rw [← pow_add,←h]; exact lower l hl)
  · exact hp _ (upper i hi) _ (upper j hj) (by rw [← pow_add,←h]; exact upper l hl)
  · exact hp _ (lower i hi) _ (upper j hj) (by rw [← pow_add,←h]; exact upper l hl)
  · exact hp _ (lower i hi) _ (lower j hj) (by rw [← pow_add,←h]; exact upper l hl)

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H1 := by
  exact geometric_extraction

end GreenAssembly.GR1H2R1H2R1H1

section FoldGR1H2R1H2R1H2R1

/- Three disjoint translates of truncated prefixes give a strict cardinality
bound unless specific differences are already realized before the threshold.
This removes all configurations with minimum at most four and shows that
a counterexample must miss every integer from 2a−4 through 2a+2.
Original Lean proof by @Deldor14. -/

namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1

open Finset

private lemma excluded_near_member (T : Finset ℕ)
    (hs : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    {c d x : ℕ} (hc : c ∈ T) (hx : x ∈ T) (hlo : c ≤ d+1) (hhi : d ≤ c+2) : x+d ∉ T := by
  intro he
  have h := hs x hx c hc (x+d) he
  omega

/-- Pack the three prefixes after translating them by d+e, e and zero. -/
def H1 : Prop := ∀ (T : Finset ℕ) (a u d e : ℕ), (∀ x ∈ T, a ≤ x) → u ∈ T →
    e ≤ a → d+e < 2*a → (∀ x ∈ T, x ≤ u → x+d ∉ T) →
    (∀ x ∈ T, x < u+a → x+e ∉ T) → (∀ x ∈ T, x ≤ u → x+(d+e) ∉ T) →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

/-- Remaining configurations have large minimum, an empty interval around twice
that minimum, and mandatory local differences for every admissible pair of offsets. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a u : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ i ∈ T, a ≤ i ∧ i ≤ u+2*a) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    5 ≤ a → u+a+1 < 3*T.card → (∀ x ∈ T, x+4 < 2*a ∨ 2*a+2 < x) →
    (∀ d e : ℕ, e ≤ a → d+e < 2*a →
      (∀ x ∈ T, x ≤ u → x+d ∉ T) → (∀ x ∈ T, x < u+a → x+e ∉ T) →
        ∃ x ∈ T, x ≤ u ∧ x+(d+e) ∈ T) →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

theorem main : H1 → H2 → OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H2 := by
  classical
  intro pack tail T a ha hmin hsep u hu hu2 _hdense
  let V := T.filter (· ≤ u+2*a)
  have haV : a ∈ V := mem_filter.mpr ⟨ha,by omega⟩
  have huV : u ∈ V := mem_filter.mpr ⟨hu,by omega⟩
  have hu2V : u+2*a ∈ V := mem_filter.mpr ⟨hu2,le_rfl⟩
  have hbounds (x : ℕ) (hx : x ∈ V) : a ≤ x ∧ x ≤ u+2*a :=
    ⟨hmin x (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩
  have hs (i : ℕ) (hi : i ∈ V) (j : ℕ) (hj : j ∈ V) (l : ℕ) (hl : l ∈ V) :
      l+1 < i+j ∨ i+j+2 < l := hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 l (mem_filter.mp hl).1
  have hh (n : ℕ) (hn : n ≤ u+2*a) : V.filter (· < n) = T.filter (· < n) := by
    ext x
    simp only [V,mem_filter]
    constructor
    · rintro ⟨⟨hx,_⟩,hl⟩; exact ⟨hx,hl⟩
    · rintro ⟨hx,hl⟩; exact ⟨⟨hx,by omega⟩,hl⟩
  rw [←hh u (by omega),←hh (u+a) (by omega),←hh (u+2*a) le_rfl]
  by_contra! hfail
  have hsize : u+a+1 < 3*V.card := by
    have hbound (n : ℕ) (hn : n ≤ u+2*a) : (V.filter (· < n)).card < V.card :=
      card_lt_card (filter_ssubset.mpr ⟨u+2*a,hu2V,by omega⟩)
    have h₁ := hbound u (by omega)
    have h₂ := hbound (u+a) (by omega)
    have h₃ := hbound (u+2*a) le_rfl
    omega
  have hhit (d e : ℕ) (he : e ≤ a) (hsum : d+e < 2*a)
      (hD : ∀ x ∈ V, x ≤ u → x+d ∉ V) (hE : ∀ x ∈ V, x < u+a → x+e ∉ V) :
      ∃ x ∈ V, x ≤ u ∧ x+(d+e) ∈ V := by
    by_contra! h
    exact (not_lt_of_ge hfail) (pack V a u d e (fun x hx => (hbounds x hx).1) huV he hsum hD hE h)
  have hapos : 2 ≤ a := by have := hs a haV a haV a haV; omega
  let b := a-1
  have hba : b+1 = a := Nat.sub_add_cancel (by omega)
  have hb (x : ℕ) (hx : x ∈ V) : x+b ∉ V := excluded_near_member V hs haV hx (by omega) (by omega)
  obtain ⟨z,hz,_,hsum⟩ := hhit b b (by omega) (by omega) (fun x hx _ => hb x hx) (fun x hx _ => hb x hx)
  have ha5 : 5 ≤ a := by
    by_contra! hl
    exact excluded_near_member V hs haV hz (by omega) (by omega) hsum
  have hgap (x : ℕ) (hx : x ∈ V) : x+4 < 2*a ∨ 2*a+2 < x := by
    by_contra! h
    have hbefore := hs a haV a haV x hx
    exact excluded_near_member V hs hx hz (by omega) (by omega) hsum
  exact (not_lt_of_ge hfail) (tail V a u haV huV hu2V hbounds hs ha5 hsize hgap hhit)

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1

end FoldGR1H2R1H2R1H2R1

namespace GreenAssembly.GR1H2R1H2R1H2R1H1

/- Disjoint translated prefixes. Original Lean proof by @Deldor14. -/

open Finset

private lemma pack_with_offsets (T : Finset ℕ) (a u d e : ℕ)
    (hmin : ∀ x ∈ T, a ≤ x) (hu : u ∈ T) (he : e ≤ a) (hde : d+e < 2*a)
    (hdiff : ∀ x ∈ T, x ≤ u → x+d ∉ T) (ediff : ∀ x ∈ T, x < u+a → x+e ∉ T)
    (bdiff : ∀ x ∈ T, x ≤ u → x+(d+e) ∉ T) :
    (T.filter (· < u)).card + (T.filter (· < u+a)).card + (T.filter (· < u+2*a)).card < u+a := by
  classical
  let U := insert u (T.filter (· < u))
  let P := U.image (· + (d+e))
  let Q := (T.filter (· < u+a)).image (· + e)
  let R := T.filter (· < u+2*a)
  have inU (x : ℕ) (hx : x ∈ U) : x ∈ T ∧ x ≤ u := by
    rcases mem_insert.mp hx with rfl | hx
    · exact ⟨hu,le_rfl⟩
    · obtain ⟨hm,hl⟩ := mem_filter.mp hx
      exact ⟨hm,hl.le⟩
  have dPQ : Disjoint P Q := by
    apply disjoint_left.mpr
    intro i hi hj
    obtain ⟨x,hx,ph⟩ := mem_image.mp hi
    obtain ⟨y,hy,qh⟩ := mem_image.mp hj
    have hxy : x+d=y := by omega
    exact hdiff x (inU x hx).1 (inU x hx).2 (hxy ▸ (mem_filter.mp hy).1)
  have dPR : Disjoint P R := by
    apply disjoint_left.mpr
    intro i hi hr
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
    exact bdiff x (inU x hx).1 (inU x hx).2 (mem_filter.mp hr).1
  have dQR : Disjoint Q R := by
    apply disjoint_left.mpr
    intro i hi hr
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hi
    exact ediff x (mem_filter.mp hx).1 (mem_filter.mp hx).2 (mem_filter.mp hr).1
  have hsub : (P ∪ Q) ∪ R ⊆ Ico a (u+2*a) := by
    intro i hi
    rcases mem_union.mp hi with hpq | hr
    · rcases mem_union.mp hpq with hp | hq
      · obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
        obtain ⟨hxT,hxu⟩ := inU x hx
        have hax := hmin x hxT
        exact mem_Ico.mpr ⟨by omega,by omega⟩
      · obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
        obtain ⟨hxT,hxu⟩ := mem_filter.mp hx
        have hax := hmin x hxT
        exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨hxT,hxu⟩ := mem_filter.mp hr
      exact mem_Ico.mpr ⟨hmin _ hxT,hxu⟩
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨dPR,dQR⟩),card_union_of_disjoint dPQ,
    Nat.card_Ico] at hcard
  have hU : U.card = (T.filter (· < u)).card+1 := card_insert_of_notMem (by simp)
  have hP : P.card = U.card := card_image_of_injective _ (add_left_injective (d+e))
  have hQ : Q.card = (T.filter (· < u+a)).card := card_image_of_injective _ (add_left_injective e)
  rw [hP,hU,hQ] at hcard
  dsimp [R] at hcard
  omega


theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1.H1 := by
  exact pack_with_offsets

end GreenAssembly.GR1H2R1H2R1H2R1H1

section FoldGR1H2R1H2R1H2R1H2R1

/- # Sumsets and reflected middle points in the three-prefix problem

For the simultaneous outer hits of Lemma 2.1 of Franchi, Gowers and Yip,
*Product-free subsets of (0,1)*, https://arxiv.org/abs/2607.06073,
thickening a sumset by four consecutive positions and reflecting the upper
part of the middle prefix give two bounds. Any remaining configuration has
at least three points between twice its minimum and the first outer hit. Its
initial points also leave a gap across four consecutive differences.
Discrete reduction and Lean proof by @Deldor14. -/

namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1
open Finset

/-- Quantitative bounds from the thickened sumset and reflected middle prefix. -/
def H1 : Prop := ∀ (T : Finset ℕ) (a u : ℕ), a ∈ T → (∀ i ∈ T, a ≤ i) →
  (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) → u ∈ T → u+2*a ∈ T →
  ((T.filter (· < u)).card + (T.filter (· < (2*a))).card + (T.filter (· < (u+2*a))).card +
    ((T.filter (· < u+a)).filter (fun y => max (2*a) u ≤ y)).card + 3 ≤ u+a) ∧
  (∀ v : ℕ, a ≤ v → (∀ d : ℕ, a < d → d ≤ v+2 → ∃ z ∈ T, z ≤ d+1 ∧ d ≤ z+2) →
    (T.filter (· < (v+1))).card + (T.filter (· < (u+a))).card + (T.filter (· < (u+2*a))).card + 2 ≤ u+a)

/-- Configurations with three intermediate points and an uncovered difference. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a u : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ i ∈ T, a ≤ i ∧ i ≤ u+2*a) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    5 ≤ a → u+a+1 < 3*T.card → (∀ x ∈ T, x+4 < 2*a ∨ 2*a+2 < x) →
    (∀ d e : ℕ, e ≤ a → d+e < 2*a →
      (∀ x ∈ T, x ≤ u → x+d ∉ T) → (∀ x ∈ T, x < u+a → x+e ∉ T) →
        ∃ x ∈ T, x ≤ u ∧ x+(d+e) ∈ T) →
    2*a < u → (T.filter (· < (2*a))).card+3 ≤ (T.filter (· < u)).card →
    (∀ v : ℕ, a ≤ v → (T.filter (· < u)).card ≤ (T.filter (· < (v+1))).card+1 → ¬ (∀ d : ℕ, a < d → d ≤ v+2 → ∃ z ∈ T, z ≤ d+1 ∧ d ≤ z+2)) →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

theorem main : H1 → H2 → OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1.H2 := by
  classical
  intro packed remaining T a u ha hu ht bounds sep minSize dense gap offsets
  have minimal (i : ℕ) (hi : i ∈ T) := (bounds i hi).1
  obtain ⟨reflected,component⟩ := packed T a u ha minimal sep hu ht
  let m := max (2*a) u
  let B := T.filter (· < u+a)
  have au := minimal u hu
  have ml : m ≤ u+a := max_le (by omega) (by omega)
  have filter_eq : B.filter (fun y => ¬m ≤ y) = T.filter (· < m) := by
    ext z
    simp only [B,mem_filter,not_le]
    constructor
    · rintro ⟨⟨zt,_⟩,zm⟩; exact ⟨zt,zm⟩
    · rintro ⟨zt,zm⟩; exact ⟨⟨zt,zm.trans_le ml⟩,zm⟩
  have card := card_filter_add_card_filter_not (s := B) (fun y => m ≤ y)
  rw [filter_eq] at card
  change (B.filter (fun y => m ≤ y)).card + (T.filter (· < m)).card = (T.filter (· < (u+a))).card at card
  change (T.filter (· < u)).card + (T.filter (· < (2*a))).card + (T.filter (· < (u+2*a))).card + (B.filter (fun y => m ≤ y)).card + 3 ≤ u+a at reflected
  change (T.filter (· < u)).card + (T.filter (· < (u+a))).card + (T.filter (· < (u+2*a))).card < u+a
  by_contra! fail
  have many : (T.filter (· < (2*a))).card+3 ≤ (T.filter (· < m)).card := by omega
  have wide : 2*a < u := by
    by_contra! h
    have e : m = 2*a := max_eq_left h
    rw [e] at many
    omega
  have e : m = u := max_eq_right wide.le
  rw [e] at many
  have gaps (v : ℕ) (av : a ≤ v) (few : (T.filter (· < u)).card ≤ (T.filter (· < (v+1))).card+1) : ¬ (∀ d : ℕ, a < d → d ≤ v+2 → ∃ z ∈ T, z ≤ d+1 ∧ d ≤ z+2) := by
    intro cov
    have save := component v av cov
    omega
  exact (not_lt_of_ge fail) (remaining T a u ha hu ht bounds sep minSize dense gap offsets wide many gaps)

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1

end FoldGR1H2R1H2R1H2R1H2R1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H1

/-
# Prefix estimates for a separated set of integers

These estimates treat the simultaneous outer hits in the discrete version of
Lemma 2.1 of Leonardo Franchi, W. T. Gowers and Fredy Yip,
*Product-free subsets of (0,1)*, https://arxiv.org/abs/2607.06073.
The four consecutive translates below arise from the separation between the
closed unit intervals and their sums. The cardinality estimate is an
application of the ordered Cauchy–Davenport inequality.
-/

namespace GreenThreeResidual
open Finset
open scoped Pointwise

def countBelow (T : Finset ℕ) (n : ℕ) : ℕ := (T.filter (· < n)).card

/-- If every sum of a point of P and a point of Q leaves three spare
positions before the endpoint, the whole thickened sumset fits in the
complement of the prefix, after translating the prefix by one position. -/
theorem packed_with_spares {T P Q R : Finset ℕ} {a N : ℕ} (ha : 0 < a)
    (hmin : ∀ x ∈ T, a ≤ x)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (psub : P ⊆ T) (qsub : Q ⊆ T)
    (span : ∀ x ∈ P, ∀ y ∈ Q, x+y+3 ≤ N)
    (spare : ∀ z ∈ R, a+1 ≤ z ∧ z < 2*a ∧ z ≤ N ∧ ∀ x ∈ T, z ≠ x+1) :
    P.card + Q.card + countBelow T N + R.card + 2 ≤ N-a := by
  classical
  let S := (P+Q) + range 4
  let C := (T.filter (· < N)).image (·+1)
  have dis : Disjoint S C := by
    apply disjoint_left.mpr
    intro n hs hc
    obtain ⟨s,hpq,d,hd,rfl⟩ := mem_add.mp hs
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hpq
    obtain ⟨z,hz,e⟩ := mem_image.mp hc
    obtain ⟨hz,_⟩ := mem_filter.mp hz
    have dlt := mem_range.mp hd
    have f := sep x (psub hx) y (qsub hy) z hz
    omega
  have sub : S ∪ C ⊆ Ico (a+1) (N+1) := by
    intro n hn
    rcases mem_union.mp hn with hs | hc
    · obtain ⟨s,hpq,d,hd,rfl⟩ := mem_add.mp hs
      obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hpq
      have xn := hmin x (psub hx)
      have yn := hmin y (qsub hy)
      have bound := span x hx y hy
      have dlt := mem_range.mp hd
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hc
      obtain ⟨hz,zn⟩ := mem_filter.mp hz
      have zl := hmin z hz
      exact mem_Ico.mpr ⟨by omega,by omega⟩
  have disR : Disjoint (S ∪ C) R := by
    apply disjoint_left.mpr
    intro n hn hr
    obtain ⟨_,lt,_,outside⟩ := spare n hr
    rcases mem_union.mp hn with hs | hc
    · obtain ⟨w,hw,d,_,rfl⟩ := mem_add.mp hs
      obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hw
      have lx := hmin x (psub hx)
      have ly := hmin y (qsub hy)
      omega
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hc
      exact outside x (mem_filter.mp hx).1 rfl
  have subR : R ⊆ Ico (a+1) (N+1) := by
    intro z hz
    obtain ⟨lo,_,hi,_⟩ := spare z hz
    exact mem_Ico.mpr ⟨lo,by omega⟩
  have cardBound := card_le_card (union_subset sub subR)
  rw [card_union_of_disjoint disR,card_union_of_disjoint dis,Nat.card_Ico] at cardBound
  have cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hP hQ
  have cd' := cauchy_davenport_add_of_linearOrder_isCancelAdd (hP.add hQ)
      (show (range 4).Nonempty from ⟨0,by decide⟩)
  have ccard : C.card = countBelow T N := card_image_of_injective _ (add_left_injective 1)
  change (P+Q).card + (range 4).card - 1 ≤ S.card at cd'
  rw [card_range] at cd'
  rw [ccard] at cardBound
  omega

theorem packed_prefixes {T P Q : Finset ℕ} {a N : ℕ} (ha : 0 < a)
    (hmin : ∀ x ∈ T, a ≤ x)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (psub : P ⊆ T) (qsub : Q ⊆ T)
    (span : ∀ x ∈ P, ∀ y ∈ Q, x+y+3 ≤ N) :
    P.card + Q.card + countBelow T N + 2 ≤ N-a := by
  simpa using packed_with_spares (R := ∅) ha hmin sep hP hQ psub qsub span (by simp)

/-- If the first component supplies all forbidden differences from a
through v+2, every point of the middle prefix is separated from the upper
hit by at least v+3. This allows the sumset argument to use the whole
middle prefix. -/
theorem component_saving {T : Finset ℕ} {a u v : ℕ} (ha : a ∈ T)
    (hmin : ∀ x ∈ T, a ≤ x)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (hu : u ∈ T) (ht : u+2*a ∈ T) (av : a ≤ v)
    (cover : ∀ d : ℕ, a < d → d ≤ v+2 → ∃ z ∈ T, z ≤ d+1 ∧ d ≤ z+2) :
    countBelow T (v+1) + countBelow T (u+a) + countBelow T (u+2*a) + 2 ≤ u+a := by
  let P := T.filter (· < v+1)
  let Q := T.filter (· < u+a)
  have hpos : 0 < a := by have hh := sep a ha a ha a ha; omega
  have upos : 0 < u := hpos.trans_le (hmin u hu)
  have p : P.Nonempty := ⟨a,mem_filter.mpr ⟨ha,by omega⟩⟩
  have q : Q.Nonempty := ⟨a,mem_filter.mpr ⟨ha,by omega⟩⟩
  have fit (x : ℕ) (hx : x ∈ P) (y : ℕ) (hy : y ∈ Q) : x+y+3 ≤ u+2*a := by
    obtain ⟨_,xv⟩ := mem_filter.mp hx
    obtain ⟨yt,ym⟩ := mem_filter.mp hy
    by_contra! fail
    let d := (u+2*a)-y
    have eq : y+d = u+2*a := by dsimp [d]; omega
    obtain ⟨z,zt,l,r⟩ := cover d (by omega) (by omega)
    have e := sep y yt z zt _ ht
    omega
  have bound := packed_prefixes hpos hmin sep p q (filter_subset _ _) (filter_subset _ _) fit
  change countBelow T (v+1) + countBelow T (u+a) + countBelow T (u+2*a) + 2 ≤ u+2*a-a at bound
  omega

/-- Reflect the part of the middle prefix above both u and twice the
minimum into the free positions strictly below the sumset. -/
theorem reflected_saving {T : Finset ℕ} {a u : ℕ} (ha : a ∈ T)
    (hmin : ∀ x ∈ T, a ≤ x)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (hu : u ∈ T) (ht : u+2*a ∈ T) :
    countBelow T u + countBelow T (2*a) + countBelow T (u+2*a) +
      ((T.filter (· < u+a)).filter (fun y => max (2*a) u ≤ y)).card + 3 ≤ u+a := by
  classical
  let P := T.filter (· ≤ u)
  let Q := T.filter (· < 2*a)
  let Y := (T.filter (· < u+a)).filter (fun y => max (2*a) u ≤ y)
  let f (y : ℕ) := u + 2*a - y - 1
  let R := Y.image f
  have amin : 0 < a := by have e := sep a ha a ha a ha; omega
  have hP : P.Nonempty := ⟨u,mem_filter.mpr ⟨hu,le_rfl⟩⟩
  have hQ : Q.Nonempty := ⟨a,mem_filter.mpr ⟨ha,by omega⟩⟩
  have span (x : ℕ) (hx : x ∈ P) (y : ℕ) (hy : y ∈ Q) : x+y+3 ≤ u+2*a := by
    obtain ⟨_,xu⟩ := mem_filter.mp hx
    obtain ⟨yt,ya⟩ := mem_filter.mp hy
    have e := sep u hu y yt _ ht
    omega
  have spec (y : ℕ) (hy : y ∈ Y) : y ∈ T ∧ u ≤ y ∧ y+2 < u+a := by
    obtain ⟨yb,ym⟩ := mem_filter.mp hy
    obtain ⟨yt,yl⟩ := mem_filter.mp yb
    have e := sep y yt a ha _ ht
    exact ⟨yt,(le_max_right _ _).trans ym,by omega⟩
  have rcard : R.card = Y.card := by
    apply card_image_of_injOn
    intro x hx y hy eq
    have l := (spec x hx).2.2
    have r := (spec y hy).2.2
    change u+2*a-x-1 = u+2*a-y-1 at eq
    omega
  have spare (z : ℕ) (hz : z ∈ R) :
      a+1 ≤ z ∧ z < 2*a ∧ z ≤ u+2*a ∧ ∀ x ∈ T, z ≠ x+1 := by
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
    obtain ⟨yt,yl,yr⟩ := spec y hy
    dsimp [f]
    refine ⟨by omega,by omega,by omega,?_⟩
    intro x xt eq
    have e := sep x xt y yt _ ht
    omega
  have b := packed_with_spares amin hmin sep hP hQ (filter_subset _ _) (filter_subset _ _) span spare
  have id : T.filter (· ≤ u) = insert u (T.filter (· < u)) := by
    ext x
    simp only [mem_filter,mem_insert]
    constructor
    · rintro ⟨hx,hl⟩
      rcases eq_or_lt_of_le hl with rfl | lt
      · exact Or.inl rfl
      · exact Or.inr ⟨hx,lt⟩
    · rintro (rfl | ⟨hx,lt⟩)
      · exact ⟨hu,le_rfl⟩
      · exact ⟨hx,lt.le⟩
  have pc : P.card = countBelow T u + 1 := by
    dsimp [P]
    rw [id,card_insert_of_notMem (by simp)]
    rfl
  rw [pc,rcard] at b
  change countBelow T u + countBelow T (2*a) + countBelow T (u+2*a) + Y.card + 3 ≤ u+a
  change countBelow T u + 1 + countBelow T (2*a) + countBelow T (u+2*a) + Y.card + 2 ≤ u+2*a-a at b
  omega

end GreenThreeResidual

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro T a u ha hmin sep hu ht
  exact ⟨GreenThreeResidual.reflected_saving ha hmin sep hu ht,
    fun v av cover => GreenThreeResidual.component_saving ha hmin sep hu ht av cover⟩

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H1

section FoldGR1H2R1H2R1H2R1H2R1H2R1

/- Finite prefix counts under simultaneous outer hits. A telescope forces dense
windows at every scale through the least element. Reflecting the middle prefix
in the last point gives six consecutive possible distances around each reflected
upper point, whenever they lie below twice the least element.
Original Lean proof by @Deldor14. -/

namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1

open Finset

/-- At minimum five, any four points in nine consecutive cells include a full
run of four. A separation of eight between extreme points leaves only its endpoints. -/
private lemma four_run_of_nine (T : Finset ℕ) (h5 : 5 ∈ T)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (t : ℕ) (hd : 3 < (T.filter (fun x => t ≤ x ∧ x < t+9)).card) :
    ∃ b : ℕ, Icc b (b+3) ⊆ T := by
  classical
  let W := T.filter (fun x => t ≤ x ∧ x < t+9)
  change 3 < W.card at hd
  have hW : W.Nonempty := card_pos.mp (by omega)
  let b := W.min' hW
  let c := W.max' hW
  have hb : b ∈ W := W.min'_mem hW
  have hc : c ∈ W := W.max'_mem hW
  obtain ⟨hbT,htb,_⟩ := mem_filter.mp hb
  obtain ⟨hcT,_,hct⟩ := mem_filter.mp hc
  have hbc := hsep b hbT 5 h5 c hcT
  by_cases hs : c ≤ b+3
  · have hsub : W ⊆ Icc b (b+3) := by
      intro x hx
      exact mem_Icc.mpr ⟨W.min'_le x hx,(W.le_max' x hx).trans hs⟩
    have hcard : (Icc b (b+3)).card ≤ W.card := by rw [Nat.card_Icc]; omega
    have he := eq_of_subset_of_card_le hsub hcard
    exact ⟨b,he ▸ (filter_subset _ T : W ⊆ T)⟩
  · have h8 : c = b+8 := by omega
    have hpair : W ⊆ {b,c} := by
      intro x hx
      have hxT := (mem_filter.mp hx).1
      have hbx := hsep b hbT 5 h5 x hxT
      have hcx := hsep x hxT 5 h5 c hcT
      have hlo : b ≤ x := W.min'_le x hx
      have hhi : x ≤ c := W.le_max' x hx
      simp only [mem_insert,mem_singleton]
      omega
    have hh := card_le_card hpair
    have hne : b ≠ c := by omega
    simp [hne] at hh
    omega

/-- A local occupancy bound at any scale through the minimum suffices. -/
def H1 : Prop := ∀ (T : Finset ℕ) (a u h : ℕ), (∀ x ∈ T, a ≤ x) → u ∈ T → u+2*a ∈ T →
    0 < h → h ≤ a → (∀ z : ℕ, (T.filter (fun x => z ≤ x ∧ x < z+3*h)).card ≤ h) →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card + (T.filter (· < u+2*a)).card < u+a

/-- A reflection supplies a quantitative lower bound for the number of local differences. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a u k d : ℕ), (∀ x ∈ T, a ≤ x) → u ∈ T → d < 2*a →
    u+2*a ≤ k+1 → k < u+3*a →
    (∀ x ∈ T, ∀ y ∈ T, x+y ≠ k) → (∀ x ∈ T, ∀ y ∈ T, x+y+d ≠ k) →
    (T.filter (· < u)).card + 1 + (T.filter (· < u+a)).card + (T.filter (· < u+2*a)).card ≤
      u+a + ((T.filter (· ≤ u)).filter (fun x => x+d ∈ T)).card

/-- The remaining sets possess a dense window at every scale, and every reflected
point in the last two windows forces nearby differences in the first window. -/
def H3 : Prop := ∀ (T : Finset ℕ) (a u : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ i ∈ T, a ≤ i ∧ i ≤ u+2*a) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    5 ≤ a → u+a+1 < 3*T.card → (∀ x ∈ T, x+4 < 2*a ∨ 2*a+2 < x) →
    (∀ d e : ℕ, e ≤ a → d+e < 2*a →
      (∀ x ∈ T, x ≤ u → x+d ∉ T) → (∀ x ∈ T, x < u+a → x+e ∉ T) →
        ∃ x ∈ T, x ≤ u ∧ x+(d+e) ∈ T) →
    2*a < u → (T.filter (· < (2*a))).card+3 ≤ (T.filter (· < u)).card →
    (∀ v : ℕ, a ≤ v → (T.filter (· < u)).card ≤ (T.filter (· < (v+1))).card+1 → ¬ (∀ d : ℕ, a < d → d ≤ v+2 → ∃ z ∈ T, z ≤ d+1 ∧ d ≤ z+2)) →
    (∀ h : ℕ, 0 < h → h ≤ a → ∃ t : ℕ, a ≤ t ∧ t+3*h ≤ u+2*a+1 ∧
      h < (T.filter (fun x => t ≤ x ∧ x < t+3*h)).card) →
    (a=5 → ∃ b : ℕ, Icc b (b+3) ⊆ T) →
    (∀ z ∈ T, ∀ d : ℕ, d < 2*a → u+2*a ≤ z+d+2 → z+d ≤ u+2*a+3 →
      ∃ x ∈ T, x ≤ u ∧ x+d ∈ T) →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

theorem main : H1 → H2 → H3 → OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1.H2 := by
  classical
  intro blocks reflect tail T a u ha hu hu2 bounds sep ha5 dense gap offsets wide many gaps
  have hmin (x : ℕ) (hx : x ∈ T) := (bounds x hx).1
  by_contra! hfail
  have crowded (h : ℕ) (hh : 0 < h) (hle : h ≤ a) :
      ∃ t : ℕ, a ≤ t ∧ t+3*h ≤ u+2*a+1 ∧
        h < (T.filter (fun x => t ≤ x ∧ x < t+3*h)).card := by
    by_contra! hno
    have hw (z : ℕ) : (T.filter (fun x => z ≤ x ∧ x < z+3*h)).card ≤ h := by
      let b := max a (min z (u+2*a+1-3*h))
      have ab : a ≤ b := le_max_left _ _
      have be : b+3*h ≤ u+2*a+1 := by dsimp [b]; omega
      have hsub : T.filter (fun x => z ≤ x ∧ x < z+3*h) ⊆
          T.filter (fun x => b ≤ x ∧ x < b+3*h) := by
        intro x hx
        obtain ⟨hx,hl,hr⟩ := mem_filter.mp hx
        obtain ⟨xa,xe⟩ := bounds x hx
        apply mem_filter.mpr
        refine ⟨hx,?_⟩
        dsimp [b]
        omega
      exact (card_le_card hsub).trans (hno b ab be)
    exact (not_lt_of_ge hfail) (blocks T a u h hmin hu hu2 hh hle hw)
  have hruns (h : a=5) : ∃ b : ℕ, Icc b (b+3) ⊆ T := by
    obtain ⟨t,_,_,hfour⟩ := crowded 3 (by decide) (by omega)
    exact four_run_of_nine T (h ▸ ha) sep t hfour
  have forced (z : ℕ) (hz : z ∈ T) (d : ℕ) (hd : d < 2*a)
      (hl : u+2*a ≤ z+d+2) (hr : z+d ≤ u+2*a+3) :
      ∃ x ∈ T, x ≤ u ∧ x+d ∈ T := by
    let s := u+2*a
    let k := min (s+1) (max (s-1) (z+d))
    have hk₁ : u+2*a ≤ k+1 := by dsimp [k,s]; omega
    have hk₂ : k < u+3*a := by dsimp [k,s]; omega
    have hn₁ (x : ℕ) (hx : x ∈ T) (y : ℕ) (hy : y ∈ T) : x+y ≠ k := by
      intro he
      have hs := sep x hx y hy (u+2*a) hu2
      dsimp [k,s] at he
      omega
    have hn₂ (x : ℕ) (hx : x ∈ T) (y : ℕ) (hy : y ∈ T) : x+y+d ≠ k := by
      intro he
      have hs := sep x hx y hy z hz
      dsimp [k,s] at he
      omega
    have hc := reflect T a u k d hmin hu hd hk₁ hk₂ hn₁ hn₂
    have hpos : 0 < ((T.filter (· ≤ u)).filter (fun x => x+d ∈ T)).card := by omega
    obtain ⟨x,hx⟩ := card_pos.mp hpos
    obtain ⟨hx,hxd⟩ := mem_filter.mp hx
    obtain ⟨hx,hxu⟩ := mem_filter.mp hx
    exact ⟨x,hx,hxu,hxd⟩
  exact (not_lt_of_ge hfail) (tail T a u ha hu hu2 bounds sep ha5 dense gap offsets wide many gaps crowded hruns forced)

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1

end FoldGR1H2R1H2R1H2R1H2R1H2R1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H1

/- Three equally spaced prefix counts. Original Lean proof by @Deldor14. -/

open Finset

private lemma prefix_growth (T : Finset ℕ) (m p : ℕ) :
    (T.filter (· < m+p)).card = (T.filter (· < m)).card +
      (T.filter (fun x => m ≤ x ∧ x < m+p)).card := by
  let P := T.filter (· < m)
  let Q := T.filter (fun x => m ≤ x ∧ x < m+p)
  have hun : T.filter (· < m+p) = P ∪ Q := by
    ext x
    by_cases hx : x ∈ T
    · simp only [P,Q,mem_filter,mem_union,hx,true_and]
      omega
    · simp [P,Q,hx]
  have hdis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨_,hl⟩ := mem_filter.mp hx
    obtain ⟨_,hr,_⟩ := mem_filter.mp hy
    omega
  rw [hun,card_union_of_disjoint hdis]

private lemma first_count (T : Finset ℕ) (a n : ℕ) (hmin : ∀ x ∈ T, a ≤ x) :
    (T.filter (· < a+n)).card ≤ n := by
  have hs : T.filter (· < a+n) ⊆ Ico a (a+n) := by
    intro x hx
    obtain ⟨hx,hxn⟩ := mem_filter.mp hx
    exact mem_Ico.mpr ⟨hmin x hx,hxn⟩
  simpa using card_le_card hs

private lemma mono_count (T : Finset ℕ) {m n : ℕ} (h : m ≤ n) :
    (T.filter (· < m)).card ≤ (T.filter (· < n)).card :=
  card_le_card (fun _ hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.trans_le h⟩)

/-- The three shifted counts telescope when their threshold moves by h. -/
private lemma three_spaced (T : Finset ℕ) (a h t : ℕ) (hh : 0 < h)
    (hmin : ∀ x ∈ T, a ≤ x)
    (hwin : ∀ z : ℕ, (T.filter (fun x => z ≤ x ∧ x < z+3*h)).card ≤ h) :
    (T.filter (· < a+t)).card + (T.filter (· < a+t+h)).card +
      (T.filter (· < a+t+2*h)).card ≤ t+2*h := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : h ≤ t
    · let r := t-h
      have er : r+h=t := Nat.sub_add_cancel ht
      have hr : r<t := by omega
      have hprev := ih r hr
      have rise := prefix_growth T (a+r) (3*h)
      have hsmall := hwin (a+r)
      rw [show a+r+3*h = a+t+2*h by omega] at rise hsmall
      rw [show a+r+h=a+t by omega,show a+r+2*h=a+t+h by omega] at hprev
      omega
    · have hs : T.filter (· < a+t+2*h) ⊆ T.filter (fun x => a ≤ x ∧ x < a+3*h) := by
        intro x hx
        obtain ⟨hx,hxn⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨hx,hmin x hx,by omega⟩
      have h1 := first_count T a t hmin
      have h3 := (card_le_card hs).trans (hwin a)
      have h2 := (mono_count T (show a+t+h ≤ a+t+2*h by omega)).trans h3
      omega

private lemma gain_at_hit (T : Finset ℕ) {t : ℕ} (ht : t ∈ T) :
    (T.filter (· < t)).card < (T.filter (· < t+1)).card :=
  card_lt_card <| Finset.ssubset_iff_subset_ne.mpr ⟨
    fun _ hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.trans (Nat.lt_succ_self _)⟩,
    fun he => by
      have h : t ∈ T.filter (· < t+1) := mem_filter.mpr ⟨ht,by omega⟩
      rw [←he] at h
      exact (lt_irrefl t) (mem_filter.mp h).2⟩

/-- At a double outer hit, every scale h through the minimum must have
a window of length 3h with at least h+1 points, or the required strict bound holds. -/
private lemma residual_of_uniform_blocks (T : Finset ℕ) (a u h : ℕ)
    (hmin : ∀ x ∈ T, a ≤ x) (hu : u ∈ T) (hu2 : u+2*a ∈ T)
    (hh : 0 < h) (hsmall : h ≤ a)
    (hwin : ∀ z : ℕ, (T.filter (fun x => z ≤ x ∧ x < z+3*h)).card ≤ h) :
    (T.filter (· < u)).card + (T.filter (· < u+a)).card + (T.filter (· < u+2*a)).card < u+a := by
  have hau := hmin u hu
  let t := u+a+1-2*h
  have he : t+2*h = u+a+1 := Nat.sub_add_cancel (by omega)
  have bound := three_spaced T a h t hh hmin hwin
  have ha₁ := mono_count T (show u+1 ≤ a+t by omega)
  have ha₂ := mono_count T (show u+a ≤ a+t+h by omega)
  rw [show a+t+2*h=u+2*a+1 by omega] at bound
  have h₁ := gain_at_hit T hu
  have h₃ := gain_at_hit T hu2
  omega

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := by
  exact residual_of_uniform_blocks

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H2

/- Reflections of the middle prefix. Original Lean proof by @Deldor14. -/

open Finset

/-- A translate and a reflection of the first two windows both fit beside the third.
The only resulting overlaps are local differences of length d. -/
private lemma reflection_count (T : Finset ℕ) (a u k d : ℕ)
    (hmin : ∀ x ∈ T, a ≤ x) (hu : u ∈ T) (hd : d < 2*a)
    (hk₁ : u+2*a ≤ k+1) (hk₂ : k < u+3*a)
    (hn₁ : ∀ x ∈ T, ∀ y ∈ T, x+y ≠ k)
    (hn₂ : ∀ x ∈ T, ∀ y ∈ T, x+y+d ≠ k) :
    (T.filter (· < u)).card + 1 + (T.filter (· < u+a)).card + (T.filter (· < u+2*a)).card ≤
      u+a + ((T.filter (· ≤ u)).filter (fun x => x+d ∈ T)).card := by
  classical
  let U := T.filter (· ≤ u)
  let V := T.filter (· < u+a)
  let R := T.filter (· < u+2*a)
  let P := U.image (· + d)
  let Q := V.image (k - ·)
  have hP : P.card = U.card := card_image_of_injective _ (add_left_injective d)
  have hQ : Q.card = V.card := card_image_iff.mpr (by
    intro x hx y hy he
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    change k-x = k-y at he
    omega)
  have hpq : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z hp hq
    obtain ⟨x,hx,hex⟩ := mem_image.mp hp
    obtain ⟨y,hy,hey⟩ := mem_image.mp hq
    obtain ⟨hxT,_⟩ := mem_filter.mp hx
    obtain ⟨hyT,hyl⟩ := mem_filter.mp hy
    exact hn₂ x hxT y hyT (by omega)
  have hqr : Disjoint Q R := by
    apply disjoint_left.mpr
    intro z hq hr
    obtain ⟨y,hy,hey⟩ := mem_image.mp hq
    obtain ⟨hyT,hyl⟩ := mem_filter.mp hy
    exact hn₁ z (mem_filter.mp hr).1 y hyT (by omega)
  have hr : (P ∪ Q) ∪ R ⊆ Ico a (u+2*a) := by
    intro z hz
    rcases mem_union.mp hz with h | h
    · rcases mem_union.mp h with hp | hq
      · obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
        obtain ⟨hxT,hxu⟩ := mem_filter.mp hx
        have := hmin x hxT
        exact mem_Ico.mpr ⟨by omega,by omega⟩
      · obtain ⟨y,hy,rfl⟩ := mem_image.mp hq
        obtain ⟨hyT,hyl⟩ := mem_filter.mp hy
        have := hmin y hyT
        exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨hzT,hzl⟩ := mem_filter.mp h
      exact mem_Ico.mpr ⟨hmin z hzT,hzl⟩
  have hpR : (P ∪ Q) ∩ R ⊆ (U.filter (fun x => x+d ∈ T)).image (· + d) := by
    intro z hz
    obtain ⟨hp,hr⟩ := mem_inter.mp hz
    rcases mem_union.mp hp with h | h
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp h
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,(mem_filter.mp hr).1⟩,rfl⟩
    · exact False.elim (disjoint_left.mp hqr h hr)
  have hcard := card_le_card hr
  have hcap := card_le_card hpR
  rw [Nat.card_Ico] at hcard
  rw [card_image_of_injective _ (add_left_injective d)] at hcap
  have htotal := card_union_add_card_inter (P ∪ Q) R
  rw [card_union_of_disjoint hpq,hP,hQ] at htotal
  have hU : U = insert u (T.filter (· < u)) := by
    ext x
    simp only [U,mem_filter,mem_insert]
    constructor
    · rintro ⟨hx,hxu⟩
      by_cases he : x=u
      · exact Or.inl he
      · exact Or.inr ⟨hx,by omega⟩
    · rintro (rfl | ⟨hx,hxu⟩)
      · exact ⟨hu,le_rfl⟩
      · exact ⟨hx,hxu.le⟩
  have hcU : U.card = (T.filter (· < u)).card+1 := by rw [hU,card_insert_of_notMem (by simp)]
  rw [hcU] at htotal
  change _ ≤ u+a + (U.filter (fun x => x+d ∈ T)).card
  change (T.filter (· < u)).card + 1 + V.card + R.card ≤ _
  omega

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H2 := by
  exact reflection_count

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H2

section FoldGR1H2R1H2R1H2R1H2R1H2R1H3R1

/- The two least remaining minima. Missing differences split the sets into short groups.
The first dense group, translated against later full groups, supplies empty positions
to compensate for their excess cardinality. Original Lean proofs by @Deldor14. -/

namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1

open Finset

/-- The family with least element five. -/
def H1 : Prop := ∀ (T : Finset ℕ) (u : ℕ), 5 ∈ T → u ∈ T → u+10 ∈ T →
    (∀ x ∈ T, 5 ≤ x ∧ x ≤ u+10) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    (∀ x ∈ T, x+4 < 10 ∨ 12 < x) → (∃ b : ℕ, Icc b (b+3) ⊆ T) →
    (T.filter (· < u)).card + (T.filter (· < u+5)).card + (T.filter (· < u+10)).card < u+5

/-- The family with least element six. -/
def H2 : Prop := ∀ (T : Finset ℕ) (u : ℕ), 6 ∈ T → u ∈ T → u+12 ∈ T →
    (∀ x ∈ T, 6 ≤ x ∧ x ≤ u+12) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    (∀ x ∈ T, x+4 < 12 ∨ 14 < x) →
    (∃ z : ℕ, 3 < (T.filter (fun x => z ≤ x ∧ x < z+9)).card) →
    (T.filter (· < u)).card + (T.filter (· < u+6)).card + (T.filter (· < u+12)).card < u+6

/-- Remaining configurations have least element at least seven. -/
def H3 : Prop := ∀ (T : Finset ℕ) (a u : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ i ∈ T, a ≤ i ∧ i ≤ u+2*a) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    7 ≤ a → u+a+1 < 3*T.card → (∀ x ∈ T, x+4 < 2*a ∨ 2*a+2 < x) →
    (∀ d e : ℕ, e ≤ a → d+e < 2*a →
      (∀ x ∈ T, x ≤ u → x+d ∉ T) → (∀ x ∈ T, x < u+a → x+e ∉ T) →
        ∃ x ∈ T, x ≤ u ∧ x+(d+e) ∈ T) →
    2*a < u → (T.filter (· < (2*a))).card+3 ≤ (T.filter (· < u)).card →
    (∀ v : ℕ, a ≤ v → (T.filter (· < u)).card ≤ (T.filter (· < (v+1))).card+1 → ¬ (∀ d : ℕ, a < d → d ≤ v+2 → ∃ z ∈ T, z ≤ d+1 ∧ d ≤ z+2)) →
    (∀ h : ℕ, 0 < h → h ≤ a → ∃ t : ℕ, a ≤ t ∧ t+3*h ≤ u+2*a+1 ∧
      h < (T.filter (fun x => t ≤ x ∧ x < t+3*h)).card) →
    (∀ z ∈ T, ∀ d : ℕ, d < 2*a → u+2*a ≤ z+d+2 → z+d ≤ u+2*a+3 →
      ∃ x ∈ T, x ≤ u ∧ x+d ∈ T) →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

theorem main : H1 → H2 → H3 → OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H3 := by
  intro five six tail T a u ha hu hu2 bounds sep h5 dense gap offsets wide many gaps crowded runs forced
  by_cases h : a=5
  · subst a
    exact five T u ha hu hu2 bounds sep gap (runs rfl)
  by_cases q : a=6
  · subst a
    obtain ⟨z,_,_,hz⟩ := crowded 3 (by decide) (by decide)
    exact six T u ha hu hu2 bounds sep gap ⟨z,hz⟩
  exact tail T a u ha hu hu2 bounds sep (by omega) dense gap offsets wide many gaps crowded forced

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1

end FoldGR1H2R1H2R1H2R1H2R1H2R1H3R1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H1

/- All configurations with least index 5. Original Lean formalization by @Deldor14. -/

open Finset
open scoped Pointwise


/-- Counting the right-hand buffers of the clusters of an integer set missing
differences four through seven. Full clusters are runs of four points. -/
private lemma buffer_count (S : Finset ℕ)
    (hD : ∀ x ∈ S, ∀ y ∈ S, y < x+4 ∨ x+7 < y) :
    let F := S.filter (fun p => Icc p (p+3) ⊆ S)
    let V := S + range 8
    3*S.card ≤ V.card+F.card ∧
    (3*S.card+1 ≤ V.card+F.card ∨ ∀ x ∈ S, ∃ p ∈ F, p ≤ x ∧ x ≤ p+3) ∧
    (F = ∅ → 10*S.card ≤ 3*V.card) := by
  classical
  let F := S.filter (fun p => Icc p (p+3) ⊆ S)
  let V := S + range 8
  let B := S.filter (fun p => ∀ x ∈ S, x < p → x+3 < p)
  let J := fun p => S.filter (fun x => p ≤ x ∧ x ≤ p+3)
  let K := fun p => J p + range 8
  have eqS : B.biUnion J = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨p,_,hxp⟩ := mem_biUnion.mp hx
      exact (mem_filter.mp hxp).1
    · intro hx
      let Q := S.filter (fun y => y ≤ x ∧ x ≤ y+3)
      have hxQ : x ∈ Q := mem_filter.mpr ⟨hx,le_rfl,by omega⟩
      let p := Q.min' ⟨x,hxQ⟩
      have hp : p ∈ Q := Q.min'_mem _
      obtain ⟨hpS,hpx,hxp⟩ := mem_filter.mp hp
      have hpB : p ∈ B := by
        refine mem_filter.mpr ⟨hpS,?_⟩
        intro y hy hyp
        by_contra! h
        have dh := hD y hy x hx
        have hyQ : y ∈ Q := mem_filter.mpr ⟨hy,by omega,by omega⟩
        have hpy : p ≤ y := Q.min'_le y hyQ
        omega
      exact mem_biUnion.mpr ⟨p,hpB,mem_filter.mpr ⟨hx,hpx,hxp⟩⟩
  have gap {p q x : ℕ} (hp : p ∈ B) (hq : q ∈ B) (hpq : p < q) (hx : x ∈ J p) :
      x+8 ≤ q := by
    obtain ⟨hxS,hpx,hxp⟩ := mem_filter.mp hx
    obtain ⟨hqS,hstart⟩ := mem_filter.mp hq
    have h1 := hstart p (mem_filter.mp hp).1 hpq
    have hxq : x < q := by omega
    have h2 := hstart x hxS hxq
    have h3 := hD x hxS q hqS
    omega
  have disK : (B : Set ℕ).PairwiseDisjoint K := by
    intro p hp q hq hne
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x,hx,i,hi,ex⟩ := mem_add.mp hz
    obtain ⟨y,hy,j,hj,ey⟩ := mem_add.mp hz'
    have hix := mem_range.mp hi
    have hjy := mem_range.mp hj
    have lpx := (mem_filter.mp hx).2.1
    have lqy := (mem_filter.mp hy).2.1
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have h := gap hp hq hpq hx
      omega
    · have h := gap hq hp hqp hy
      omega
  have subJK (p : ℕ) : J p ⊆ K p := fun x hx => by
    exact mem_add.mpr ⟨x,hx,0,by decide,by simp⟩
  have disJ : (B : Set ℕ).PairwiseDisjoint J := by
    intro p hp q hq hne
    exact (disK hp hq hne).mono (subJK p) (subJK q)
  have eqV : B.biUnion K = V := by
    ext z
    constructor
    · intro hz
      obtain ⟨p,_,y⟩ := mem_biUnion.mp hz
      obtain ⟨v,hv,i,hi,e⟩ := mem_add.mp y
      exact mem_add.mpr ⟨v,(mem_filter.mp hv).1,i,hi,e⟩
    · intro hz
      obtain ⟨x,hx,i,hi,e⟩ := mem_add.mp hz
      rw [←eqS] at hx
      obtain ⟨p,hp,hxp⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨p,hp,mem_add.mpr ⟨x,hxp,i,hi,e⟩⟩
  have hJS : ∑ p ∈ B, (J p).card = S.card := by rw [←card_biUnion disJ,eqS]
  have hKV : ∑ p ∈ B, (K p).card = V.card := by rw [←card_biUnion disK,eqV]
  have jsub (p : ℕ) : J p ⊆ Icc p (p+3) := fun x hx => mem_Icc.mpr (mem_filter.mp hx).2
  have jfour (p : ℕ) : (J p).card ≤ 4 := by
    have h := card_le_card (jsub p)
    rw [Nat.card_Icc] at h
    omega
  have jfull {p : ℕ} (hp : p ∈ B) (h4 : (J p).card = 4) : p ∈ F := by
    have he : J p = Icc p (p+3) := eq_of_subset_of_card_le (jsub p) (by rw [Nat.card_Icc]; omega)
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,he ▸ (filter_subset _ S : J p ⊆ S)⟩
  have buf {p : ℕ} (hp : p ∈ B) : (J p).card+7 ≤ (K p).card := by
    have h1 : (J p).Nonempty := ⟨p,mem_filter.mpr ⟨(mem_filter.mp hp).1,le_rfl,by omega⟩⟩
    have hb := cauchy_davenport_add_of_linearOrder_isCancelAdd h1 (show (range 8).Nonempty from ⟨0,by decide⟩)
    change (J p).card+(range 8).card-1 ≤ (K p).card at hb
    rw [card_range] at hb
    omega
  have countF : (∑ p ∈ B, if p ∈ F then 1 else 0) ≤ F.card := by
    rw [←card_filter]
    exact card_le_card (fun _ hx => (mem_filter.mp hx).2)
  have cost {p : ℕ} (hp : p ∈ B) :
      3*(J p).card + (if p ∈ F then 0 else 1) ≤ (K p).card + (if p ∈ F then 1 else 0) := by
    have hb := buf hp
    have h4 := jfour p
    by_cases hf : p ∈ F
    · simp only [hf,if_true]; omega
    · have h3 : (J p).card ≠ 4 := fun h => hf (jfull hp h)
      simp only [hf,if_false]; omega
  have total := sum_le_sum (s:=B) (fun p hp => cost hp)
  rw [sum_add_distrib,sum_add_distrib,←mul_sum,hJS,hKV] at total
  change 3*S.card ≤ V.card+F.card ∧ (3*S.card+1 ≤ V.card+F.card ∨ ∀ x ∈ S, ∃ p ∈ F, p ≤ x ∧ x ≤ p+3) ∧ (F=∅ → 10*S.card ≤ 3*V.card)
  refine ⟨by omega,?_,?_⟩
  · by_cases hbad : ∃ p ∈ B, p ∉ F
    · left
      obtain ⟨p,hp,hpF⟩ := hbad
      have hpos : 0 < ∑ x ∈ B, if x ∈ F then 0 else 1 := by
        apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
        exact ⟨p,hp,by simp [hpF]⟩
      omega
    · right
      intro x hx
      rw [←eqS] at hx
      obtain ⟨p,hp,hxp⟩ := mem_biUnion.mp hx
      exact ⟨p,Classical.byContradiction (fun hn => hbad ⟨p,hp,hn⟩),(mem_filter.mp hxp).2⟩
  · intro hF
    have small {p : ℕ} (hp : p ∈ B) : 10*(J p).card ≤ 3*(K p).card := by
      have hb := buf hp
      have h4 := jfour p
      have h3 : (J p).card ≠ 4 := fun e => by have hh := jfull hp e; rw [hF] at hh; exact notMem_empty _ hh
      omega
    have hs := sum_le_sum (s:=B) (fun _ hp => small hp)
    rwa [←mul_sum,←mul_sum,hJS,hKV] at hs


private lemma run_start_mem {T : Finset ℕ} {p : ℕ} (h : Icc p (p+3) ⊆ T) : p ∈ T :=
  h (mem_Icc.mpr ⟨le_rfl,by omega⟩)

private lemma after_run {T : Finset ℕ}
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+4 ∨ x+7 < y)
    {p x : ℕ} (hp : Icc p (p+3) ⊆ T) (hx : x ∈ T) (hxp : x < p) : x+7 < p := by
  by_cases h : p ≤ x+4
  · have hs : x+4 ∈ T := hp (mem_Icc.mpr ⟨h,by omega⟩)
    have := hD x hx (x+4) hs
    omega
  · have := hD x hx p (run_start_mem hp)
    omega

private lemma run_spacing {T : Finset ℕ}
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+4 ∨ x+7 < y)
    {p q : ℕ} (hp : Icc p (p+3) ⊆ T) (hq : Icc q (q+3) ⊆ T) (hpq : p < q) :
    p+11 ≤ q := by
  have h1 := after_run hD hq (run_start_mem hp) hpq
  have hx : p+3 ∈ T := hp (mem_Icc.mpr ⟨by omega,le_rfl⟩)
  have h := after_run hD hq hx (by omega)
  omega

private lemma initial_cost (T : Finset ℕ) (b : ℕ) (h5 : 5 ∈ T)
    (hmin : ∀ x ∈ T, 5 ≤ x)
    (gap : ∀ x ∈ T, x+4 < 10 ∨ 12 < x)
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+4 ∨ x+7 < y)
    (hfull : Icc b (b+3) ⊆ T) (hfirst : ∀ p, Icc p (p+3) ⊆ T → b ≤ p)
    (small : ∀ E : Finset ℕ, E ⊆ T → (E.filter (fun p => Icc p (p+3) ⊆ E)) = ∅ →
      10*E.card ≤ 3*(E + range 8).card) :
    13 ≤ b ∧ 10*(T.filter (· < b)).card+29 ≤ 3*b := by
  classical
  have hb := run_start_mem hfull
  have h5b : 5 ≤ b := hmin b hb
  have hb13 : 13 ≤ b := by
    have hg := gap b hb
    have h6 := hfull (show b+1 ∈ Icc b (b+3) from mem_Icc.mpr ⟨by omega,by omega⟩)
    have hg' := gap (b+1) h6
    omega
  let A := T.filter (· < b)
  let E := A.erase 5
  have ha5 : 5 ∈ A := mem_filter.mpr ⟨h5,by omega⟩
  have sub (x : ℕ) (hx : x ∈ E) : x ∈ T ∧ 13 ≤ x ∧ x+7 < b := by
    obtain ⟨hne,ha⟩ := mem_erase.mp hx
    obtain ⟨hxT,hxb⟩ := mem_filter.mp ha
    have hg := gap x hxT
    have hm := hmin x hxT
    exact ⟨hxT,by omega,after_run hD hfull hxT hxb⟩
  have hsub : E ⊆ T := fun x hx => (sub x hx).1
  have empty : E.filter (fun p => Icc p (p+3) ⊆ E) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp,hr⟩ := mem_filter.mp hp
    have hb' := hfirst p (hr.trans hsub)
    have hx := (sub p hp).2.2
    omega
  have room : E+range 8 ⊆ Ico 13 b := by
    intro z hz
    obtain ⟨x,hx,i,hi,rfl⟩ := mem_add.mp hz
    obtain ⟨_,h13,hhi⟩ := sub x hx
    have hir := mem_range.mp hi
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have hs := small E hsub empty
  have bound := card_le_card room
  rw [Nat.card_Ico] at bound
  have er : E.card+1=A.card := card_erase_add_one ha5
  change 13 ≤ b ∧ 10*A.card+29 ≤ 3*b
  exact ⟨hb13,by omega⟩

private lemma late_runs (T F : Finset ℕ) (s b : ℕ) (hbs : b ≤ s)
    (hup : ∀ x ∈ T, x ≤ s)
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+4 ∨ x+7 < y)
    (full : ∀ p ∈ F, Icc p (p+3) ⊆ T) :
    11*(F.filter (fun p => s+1 < b+p)).card ≤ b+6 := by
  classical
  let L := F.filter (fun p => s+1 < b+p)
  let J := fun p => Ico p (p+11)
  have dis : (L : Set ℕ).PairwiseDisjoint J := by
    intro p hp q hq hne
    have hpf := full p (mem_filter.mp hp).1
    have hqf := full q (mem_filter.mp hq).1
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨hpz,hzp⟩ := mem_Ico.mp hz
    obtain ⟨hqz,hzq⟩ := mem_Ico.mp hz'
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have := run_spacing hD hpf hqf hpq
      omega
    · have := run_spacing hD hqf hpf hqp
      omega
  have hs : L.biUnion J ⊆ Ico (s+2-b) (s+8) := by
    intro z hz
    obtain ⟨p,hp,hz⟩ := mem_biUnion.mp hz
    obtain ⟨hpF,hpb⟩ := mem_filter.mp hp
    have hh := hup (p+3) (full p hpF (mem_Icc.mpr ⟨by omega,le_rfl⟩))
    obtain ⟨hpz,hzp⟩ := mem_Ico.mp hz
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have hc := card_le_card hs
  rw [card_biUnion dis,Nat.card_Ico] at hc
  have hsize (p : ℕ) : (J p).card = 11 := by simp [J]
  simpa [hsize,mul_comm,show s+8-(s+2-b)=b+6 by omega] using hc

private lemma spare_positions (T S F : Finset ℕ) (s b : ℕ) (sub : S ⊆ T) (hb : Icc b (b+3) ⊆ T)
    (full : ∀ p ∈ F, Icc p (p+3) ⊆ T)
    (bounds : ∀ x ∈ S, b ≤ x ∧ x ≤ s)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    (S + range 8).card + (F.filter (fun p => b+p ≤ s+1)).card ≤ s+8-b := by
  classical
  let G := F.filter (fun p => b+p ≤ s+1)
  let D := G.image (· + (b+6))
  have hd : Disjoint (S+range 8) D := by
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨y,hy,i,hi,ey⟩ := mem_add.mp hz
    obtain ⟨p,hp,ep⟩ := mem_image.mp hz'
    have hlo := mem_range.mp hi
    let w := 6-i
    let v := min 3 w
    have h1 : b+v ∈ T := hb (mem_Icc.mpr ⟨by omega,by dsimp [v]; omega⟩)
    have h2 : p+(w-v) ∈ T := full p (mem_filter.mp hp).1 (mem_Icc.mpr ⟨by omega,by dsimp [v,w]; omega⟩)
    have h := sep (b+v) h1 (p+(w-v)) h2 y (sub hy)
    dsimp [v,w] at h
    omega
  have hs : (S+range 8) ∪ D ⊆ Ico b (s+8) := by
    intro z hz
    rcases mem_union.mp hz with h | h
    · obtain ⟨y,hy,i,hi,rfl⟩ := mem_add.mp h
      have hi' := mem_range.mp hi
      obtain ⟨h1,h2⟩ := bounds y hy
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨p,hp,rfl⟩ := mem_image.mp h
      have h2 := (mem_filter.mp hp).2
      exact mem_Ico.mpr ⟨by omega,by omega⟩
  have hcard := card_le_card hs
  rwa [card_union_of_disjoint hd,Nat.card_Ico,show D.card=G.card from
      card_image_of_injective _ (add_left_injective (b+6))] at hcard


private lemma increase_at (T : Finset ℕ) {x m n : ℕ} (hx : x ∈ T)
    (hm : m ≤ x) (hn : x < n) :
    (T.filter (· < m)).card < (T.filter (· < n)).card := by
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨fun _ h => mem_filter.mpr
    ⟨(mem_filter.mp h).1,by have := (mem_filter.mp h).2; omega⟩,?_⟩
  intro he
  have h : x ∈ T.filter (· < n) := mem_filter.mpr ⟨hx,hn⟩
  rw [←he] at h
  have := (mem_filter.mp h).2
  omega

/-- All double-hit configurations with least index five are resolved after
the initial forbidden interval and the four-run condition. -/
private lemma case_five (T : Finset ℕ) (u : ℕ) (h5 : 5 ∈ T) (hu : u ∈ T) (hs : u+10 ∈ T)
    (bounds : ∀ x ∈ T, 5 ≤ x ∧ x ≤ u+10)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (gap : ∀ x ∈ T, x+4 < 10 ∨ 12 < x) (runs : ∃ b : ℕ, Icc b (b+3) ⊆ T) :
    (T.filter (· < u)).card + (T.filter (· < u+5)).card + (T.filter (· < u+10)).card < u+5 := by
  classical
  let s := u+10
  let R := T.filter (fun p => Icc p (p+3) ⊆ T)
  obtain ⟨z,hz⟩ := runs
  have rz : z ∈ R := mem_filter.mpr ⟨hz (mem_Icc.mpr ⟨le_rfl,by omega⟩),hz⟩
  let b := R.min' ⟨z,rz⟩
  have rb : b ∈ R := R.min'_mem _
  obtain ⟨hbT,hbfull⟩ := mem_filter.mp rb
  have hfirst (p : ℕ) (hp : Icc p (p+3) ⊆ T) : b ≤ p :=
    R.min'_le p (mem_filter.mpr ⟨hp (mem_Icc.mpr ⟨le_rfl,by omega⟩),hp⟩)
  have hdif (x : ℕ) (hx : x ∈ T) (y : ℕ) (hy : y ∈ T) : y < x+4 ∨ x+7 < y := by
    have h := sep x hx 5 h5 y hy
    omega
  let A := T.filter (· < b)
  let S := T.filter (b ≤ ·)
  have sub : S ⊆ T := filter_subset _ _
  have bds (x : ℕ) (hx : x ∈ S) : b ≤ x ∧ x ≤ s := ⟨(mem_filter.mp hx).2,(bounds x (sub hx)).2⟩
  have smax : b ≤ s := (bounds b hbT).2
  have hsS : s ∈ S := mem_filter.mpr ⟨hs,smax⟩
  have splitCount : A.card+S.card=T.card := by
    simpa only [A,S,not_lt] using card_filter_add_card_filter_not (s:=T) (fun x => x<b)
  obtain ⟨hb13,first⟩ := initial_cost T b h5 (fun x hx => (bounds x hx).1) gap hdif hbfull hfirst
    (fun E hET => (buffer_count E (fun x hx y hy => hdif x (hET hx) y (hET hy))).2.2)
  change 10*A.card+29 ≤ 3*b at first
  let F := S.filter (fun p => Icc p (p+3) ⊆ S)
  let V := S + range 8
  have full (p : ℕ) (hp : p ∈ F) : Icc p (p+3) ⊆ T := (mem_filter.mp hp).2.trans sub
  have late := late_runs T F s b smax (fun x hx => (bounds x hx).2) hdif full
  have slots := spare_positions T S F s b sub hbfull full bds sep
  change V.card+(F.filter (fun p => b+p ≤ s+1)).card ≤ s+8-b at slots
  have cuts := card_filter_add_card_filter_not (s:=F) (fun p => b+p ≤ s+1)
  simp only [not_le] at cuts
  obtain ⟨cost,extra,_⟩ := buffer_count S (fun x hx y hy => hdif x (sub hx) y (sub hy))
  change 3*S.card ≤ V.card+F.card at cost
  change 3*S.card+1 ≤ V.card+F.card ∨ ∀ x ∈ S, ∃ p ∈ F, p ≤ x ∧ x ≤ p+3 at extra
  have paid : 3*A.card+(F.filter (fun p => s+1 < b+p)).card+9 ≤ b := by omega
  have total : 3*T.card+1 ≤ s := by omega
  have x1 := increase_at T hu (le_refl u) (show u<u+5 by omega)
  have x2 : (T.filter (· < u+5)).card ≤ (T.filter (· < s)).card :=
    card_le_card (fun _ hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,by
      dsimp [s]; have := (mem_filter.mp hx).2; omega⟩)
  have x3 : (T.filter (· < s)).card < T.card := card_lt_card
    (filter_ssubset.mpr ⟨s,hs,by omega⟩)
  change (T.filter (· < u)).card + (T.filter (· < u+5)).card + (T.filter (· < s)).card < u+5
  have es : s=u+10 := rfl
  rcases extra with slack | allFull
  · omega
  · obtain ⟨p,hp,hps,hsp⟩ := allFull s hsS
    have hp3 : p+3 ≤ s := (bounds _ (full p hp (mem_Icc.mpr ⟨by omega,le_rfl⟩))).2
    have hx : s-1 ∈ T := full p hp (mem_Icc.mpr ⟨by omega,by omega⟩)
    have x4 := increase_at T hx (show u+5 ≤ s-1 by omega) (show s-1 < s by omega)
    omega


theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1.H1 := by
  exact case_five

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H2

/- All configurations with least index 6. Original Lean formalization by @Deldor14. -/

open Finset
open scoped Pointwise


/-- Buffer counting for sets avoiding differences five through eight. -/
private lemma buffer_count (S : Finset ℕ)
    (hD : ∀ x ∈ S, ∀ y ∈ S, y < x+5 ∨ x+8 < y) :
    let F := S.filter (fun p => Icc p (p+4) ⊆ S)
    let V := S + range 9
    (∀ s ∈ S, (∀ x ∈ S, x ≤ s) → 3*S.card+8 ≤ V.card+2*F.card+
      2*(S.filter (fun x => s ≤ x+4)).card) ∧
    ((∀ p ∈ S, (S.filter (fun x => p ≤ x ∧ x ≤ p+4)).card ≤ 3) →
      11*S.card ≤ 3*V.card) := by
  classical
  let F := S.filter (fun p => Icc p (p+4) ⊆ S)
  let V := S + range 9
  let B := S.filter (fun p => ∀ x ∈ S, x < p → x+4 < p)
  let J := fun p => S.filter (fun x => p ≤ x ∧ x ≤ p+4)
  let K := fun p => J p + range 9
  have eqS : B.biUnion J = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨p,_,hxp⟩ := mem_biUnion.mp hx
      exact (mem_filter.mp hxp).1
    · intro hx
      let Q := S.filter (fun y => y ≤ x ∧ x ≤ y+4)
      have hxQ : x ∈ Q := mem_filter.mpr ⟨hx,le_rfl,by omega⟩
      let p := Q.min' ⟨x,hxQ⟩
      have hp : p ∈ Q := Q.min'_mem _
      obtain ⟨hpS,hpx,hxp⟩ := mem_filter.mp hp
      have hpB : p ∈ B := by
        refine mem_filter.mpr ⟨hpS,?_⟩
        intro y hy hyp
        by_contra! h
        have dh := hD y hy x hx
        have hyQ : y ∈ Q := mem_filter.mpr ⟨hy,by omega,by omega⟩
        have hpy : p ≤ y := Q.min'_le y hyQ
        omega
      exact mem_biUnion.mpr ⟨p,hpB,mem_filter.mpr ⟨hx,hpx,hxp⟩⟩
  have gap {p q x : ℕ} (hp : p ∈ B) (hq : q ∈ B) (hpq : p < q) (hx : x ∈ J p) :
      x+9 ≤ q := by
    obtain ⟨hxS,hpx,hxp⟩ := mem_filter.mp hx
    obtain ⟨hqS,hstart⟩ := mem_filter.mp hq
    have h1 := hstart p (mem_filter.mp hp).1 hpq
    have hxq : x < q := by omega
    have h2 := hstart x hxS hxq
    have h3 := hD x hxS q hqS
    omega
  have disK : (B : Set ℕ).PairwiseDisjoint K := by
    intro p hp q hq hne
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x,hx,i,hi,ex⟩ := mem_add.mp hz
    obtain ⟨y,hy,j,hj,ey⟩ := mem_add.mp hz'
    have hix := mem_range.mp hi
    have hjy := mem_range.mp hj
    have lpx := (mem_filter.mp hx).2.1
    have lqy := (mem_filter.mp hy).2.1
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have h := gap hp hq hpq hx
      omega
    · have h := gap hq hp hqp hy
      omega
  have subJK (p : ℕ) : J p ⊆ K p := fun x hx => by
    exact mem_add.mpr ⟨x,hx,0,by decide,by simp⟩
  have disJ : (B : Set ℕ).PairwiseDisjoint J := by
    intro p hp q hq hne
    exact (disK hp hq hne).mono (subJK p) (subJK q)
  have eqV : B.biUnion K = V := by
    ext z
    constructor
    · intro hz
      obtain ⟨p,_,y⟩ := mem_biUnion.mp hz
      obtain ⟨v,hv,i,hi,e⟩ := mem_add.mp y
      exact mem_add.mpr ⟨v,(mem_filter.mp hv).1,i,hi,e⟩
    · intro hz
      obtain ⟨x,hx,i,hi,e⟩ := mem_add.mp hz
      rw [←eqS] at hx
      obtain ⟨p,hp,hxp⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨p,hp,mem_add.mpr ⟨x,hxp,i,hi,e⟩⟩
  have hJS : ∑ p ∈ B, (J p).card = S.card := by rw [←card_biUnion disJ,eqS]
  have hKV : ∑ p ∈ B, (K p).card = V.card := by rw [←card_biUnion disK,eqV]
  have jsub (p : ℕ) : J p ⊆ Icc p (p+4) := fun x hx => mem_Icc.mpr (mem_filter.mp hx).2
  have jfour (p : ℕ) : (J p).card ≤ 5 := by
    have h := card_le_card (jsub p)
    rw [Nat.card_Icc] at h
    omega
  have jfull {p : ℕ} (hp : p ∈ B) (h4 : (J p).card = 5) : p ∈ F := by
    have he : J p = Icc p (p+4) := eq_of_subset_of_card_le (jsub p) (by rw [Nat.card_Icc]; omega)
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,he ▸ (filter_subset _ S : J p ⊆ S)⟩
  have buf {p : ℕ} (hp : p ∈ B) : (J p).card+8 ≤ (K p).card := by
    have h1 : (J p).Nonempty := ⟨p,mem_filter.mpr ⟨(mem_filter.mp hp).1,le_rfl,by omega⟩⟩
    have hb := cauchy_davenport_add_of_linearOrder_isCancelAdd h1 (show (range 9).Nonempty from ⟨0,by decide⟩)
    change (J p).card+(range 9).card-1 ≤ (K p).card at hb
    rw [card_range] at hb
    omega
  have countF : (∑ p ∈ B, if p ∈ F then 1 else 0) ≤ F.card := by
    rw [←card_filter]
    exact card_le_card (fun _ hx => (mem_filter.mp hx).2)
  constructor
  · intro s hs _hmax
    rw [←eqS] at hs
    obtain ⟨e,he,hes⟩ := mem_biUnion.mp hs
    have ex : ∀ p ∈ B, 3*(J p).card + (if e=p then 8 else 0) ≤
        (K p).card + 2*(if p ∈ F then 1 else 0) + (if e=p then 2*(J p).card else 0) := by
      intro p hp
      have hb := buf hp
      have h5 := jfour p
      by_cases hlast : e=p
      · simp only [hlast,if_true]; split <;> omega
      · simp only [hlast,if_false,add_zero]
        by_cases hf : p ∈ F
        · simp only [hf,if_true]; omega
        · have hn : (J p).card ≠ 5 := fun eq => hf (jfull hp eq)
          simp only [hf,if_false]; omega
    have cost := sum_le_sum ex
    simp only [sum_add_distrib,←mul_sum,hJS,hKV,Finset.sum_ite_eq,he,if_true] at cost
    have subEnd : J e ⊆ S.filter (fun x => s ≤ x+4) := by
      intro x hx
      obtain ⟨hxS,hex,_⟩ := mem_filter.mp hx
      have se := (mem_filter.mp hes).2.2
      exact mem_filter.mpr ⟨hxS,by omega⟩
    have cs := card_le_card subEnd
    change 3*S.card+8 ≤ V.card+2*F.card+2*(S.filter (fun x => s ≤ x+4)).card
    omega
  · intro near
    have small {p : ℕ} (hp : p ∈ B) : 11*(J p).card ≤ 3*(K p).card := by
      have hj : (J p).card ≤ 3 := near p (mem_filter.mp hp).1
      have hb := buf hp
      omega
    have cost := sum_le_sum (s:=B) (fun _ hp => small hp)
    rwa [←mul_sum,←mul_sum,hJS,hKV] at cost


private lemma mem_run {T : Finset ℕ} {p : ℕ} (h : Icc p (p+4) ⊆ T) : p ∈ T :=
  h (mem_Icc.mpr ⟨le_rfl,by omega⟩)

private lemma after_run {T : Finset ℕ}
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+5 ∨ x+8 < y)
    {p x : ℕ} (hp : Icc p (p+4) ⊆ T) (hx : x ∈ T) (hxp : x < p) : x+8 < p := by
  by_cases h : p ≤ x+5
  · have hs : x+5 ∈ T := hp (mem_Icc.mpr ⟨h,by omega⟩)
    have := hD x hx (x+5) hs
    omega
  · have := hD x hx p (mem_run hp)
    omega

private lemma run_spacing {T : Finset ℕ}
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+5 ∨ x+8 < y)
    {p q : ℕ} (hp : Icc p (p+4) ⊆ T) (hq : Icc q (q+4) ⊆ T) (hpq : p < q) :
    p+13 ≤ q := by
  have h1 := after_run hD hq (mem_run hp) hpq
  have hx : p+4 ∈ T := hp (mem_Icc.mpr ⟨by omega,le_rfl⟩)
  have h := after_run hD hq hx (by omega)
  omega

private lemma initial_cost (T : Finset ℕ) (b : ℕ) (hb : b ∈ T)
    (hmin : ∀ x ∈ T, 6 ≤ x) (gap : ∀ x ∈ T, x+4 < 12 ∨ 14 < x)
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+5 ∨ x+8 < y)
    (hb4 : 4 ≤ (T.filter (fun x => b ≤ x ∧ x ≤ b+4)).card)
    (first : ∀ p ∈ T, 4 ≤ (T.filter (fun x => p ≤ x ∧ x ≤ p+4)).card → b ≤ p)
    (small : ∀ E : Finset ℕ, E ⊆ T →
      (∀ p ∈ E, (E.filter (fun x => p ≤ x ∧ x ≤ p+4)).card ≤ 3) →
        11*E.card ≤ 3*(E+range 9).card) :
    15 ≤ b ∧ 11*(T.filter (· < b)).card+23 ≤ 3*b := by
  classical
  let J := T.filter (fun x => b ≤ x ∧ x ≤ b+4)
  change 4 ≤ J.card at hb4
  have bmin := hmin b hb
  have hb15 : 15 ≤ b := by
    by_contra! hl
    have g := gap b hb
    have sub : J ⊆ Icc 6 7 := by
      intro x hx
      obtain ⟨hxT,_,hxb⟩ := mem_filter.mp hx
      have hg := gap x hxT
      exact mem_Icc.mpr ⟨hmin x hxT,by omega⟩
    have h := card_le_card sub
    rw [Nat.card_Icc] at h
    omega
  let A := T.filter (· < b)
  let E := A.filter (15 ≤ ·)
  have sub (x : ℕ) (hx : x ∈ E) : x ∈ T ∧ 15 ≤ x ∧ x+8 < b := by
    obtain ⟨ha,h15⟩ := mem_filter.mp hx
    obtain ⟨hxT,hxb⟩ := mem_filter.mp ha
    have hlow := hD x hxT b hb
    refine ⟨hxT,h15,?_⟩
    by_contra! h
    have hsub : J ⊆ T.filter (fun z => x ≤ z ∧ z ≤ x+4) := by
      intro z hz
      obtain ⟨hzT,hbz,hzb⟩ := mem_filter.mp hz
      have hd := hD x hxT z hzT
      exact mem_filter.mpr ⟨hzT,by omega,by omega⟩
    have fb := first x hxT (hb4.trans (card_le_card hsub))
    omega
  have subET : E ⊆ T := fun x hx => (sub x hx).1
  have sparse (p : ℕ) (hp : p ∈ E) : (E.filter (fun x => p ≤ x ∧ x ≤ p+4)).card ≤ 3 := by
    have hj : E.filter (fun x => p ≤ x ∧ x ≤ p+4) ⊆ T.filter (fun x => p ≤ x ∧ x ≤ p+4) :=
      fun x hx => mem_filter.mpr ⟨subET (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩
    by_contra! h
    have hb' := first p (subET hp) (h.trans_le (card_le_card hj))
    have hx := (sub p hp).2.2
    omega
  have room : E+range 9 ⊆ Ico 15 b := by
    intro z hz
    obtain ⟨x,hx,i,hi,rfl⟩ := mem_add.mp hz
    obtain ⟨_,h15,hb'⟩ := sub x hx
    have hi' := mem_range.mp hi
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have rest : A.filter (fun x => ¬15 ≤ x) ⊆ Icc 6 7 := by
    intro x hx
    obtain ⟨hxA,hl⟩ := mem_filter.mp hx
    have hxT := (mem_filter.mp hxA).1
    have hg := gap x hxT
    exact mem_Icc.mpr ⟨hmin x hxT,by omega⟩
  have split := card_filter_add_card_filter_not (s:=A) (15 ≤ ·)
  have hc := card_le_card rest
  rw [Nat.card_Icc] at hc
  have hE := small E subET sparse
  have hV := card_le_card room
  rw [Nat.card_Ico] at hV
  change E.card+_ = A.card at split
  change 15 ≤ b ∧ 11*A.card+23 ≤ 3*b
  exact ⟨hb15,by omega⟩

private lemma late_runs (T F : Finset ℕ) (s b : ℕ) (hbs : b ≤ s)
    (hup : ∀ x ∈ T, x ≤ s)
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+5 ∨ x+8 < y)
    (full : ∀ p ∈ F, Icc p (p+4) ⊆ T) :
    13*(F.filter (fun p => s < b+p)).card ≤ b+8 := by
  classical
  let L := F.filter (fun p => s < b+p)
  let J := fun p => Ico p (p+13)
  have dis : (L : Set ℕ).PairwiseDisjoint J := by
    intro p hp q hq hne
    have hpf := full p (mem_filter.mp hp).1
    have hqf := full q (mem_filter.mp hq).1
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨hpz,hzp⟩ := mem_Ico.mp hz
    obtain ⟨hqz,hzq⟩ := mem_Ico.mp hz'
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have := run_spacing hD hpf hqf hpq
      omega
    · have := run_spacing hD hqf hpf hqp
      omega
  have hs : L.biUnion J ⊆ Ico (s+1-b) (s+9) := by
    intro z hz
    obtain ⟨p,hp,hz⟩ := mem_biUnion.mp hz
    obtain ⟨hpF,hpb⟩ := mem_filter.mp hp
    have hh := hup (p+4) (full p hpF (mem_Icc.mpr ⟨by omega,le_rfl⟩))
    obtain ⟨hpz,hzp⟩ := mem_Ico.mp hz
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  have hc := card_le_card hs
  rw [card_biUnion dis,Nat.card_Ico] at hc
  have hsize (p : ℕ) : (J p).card = 13 := by simp [J]
  simpa [hsize,mul_comm,show s+9-(s+1-b)=b+8 by omega] using hc

private lemma spare_positions (T S F : Finset ℕ) (s b c : ℕ) (sub : S ⊆ T) (hb : b ∈ T)
    (hc : c ∈ T) (hbc₁ : b+3 ≤ c) (hbc₂ : c ≤ b+4)
    (full : ∀ p ∈ F, Icc p (p+4) ⊆ T)
    (bounds : ∀ x ∈ S, b ≤ x ∧ x ≤ s)
    (hD : ∀ x ∈ T, ∀ y ∈ T, y < x+5 ∨ x+8 < y)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    (S+range 9).card + 2*(F.filter (fun p => b+p ≤ s)).card ≤ s+9-b := by
  classical
  let G := F.filter (fun p => b+p ≤ s)
  let J := fun p => Ico (b+p+7) (b+p+9)
  let D := G.biUnion J
  have dJ : (G : Set ℕ).PairwiseDisjoint J := by
    intro p hp q hq hne
    apply disjoint_left.mpr
    intro v hv hv'
    obtain ⟨hl,hr⟩ := mem_Ico.mp hv
    obtain ⟨hl',hr'⟩ := mem_Ico.mp hv'
    have pf := full p (mem_filter.mp hp).1
    have qf := full q (mem_filter.mp hq).1
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have := run_spacing hD pf qf hpq
      omega
    · have := run_spacing hD qf pf hqp
      omega
  have hd : Disjoint (S+range 9) D := by
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨y,hy,i,hi,ey⟩ := mem_add.mp hz
    obtain ⟨p,hp,hzJ⟩ := mem_biUnion.mp hz'
    obtain ⟨hjl,hjr⟩ := mem_Ico.mp hzJ
    have hir := mem_range.mp hi
    let w := min 7 (y-(b+p))
    have reach {j : ℕ} (hj : j ≤ 4) : p+j ∈ T :=
      full p (mem_filter.mp hp).1 (mem_Icc.mpr ⟨by omega,by omega⟩)
    by_cases h : w ≤ 4
    · have he := sep b hb (p+w) (reach h) y (sub hy)
      dsimp [w] at h he
      omega
    · have hh : b+w-c ≤ 4 := by dsimp [w] at *; omega
      have he := sep c hc (p+(b+w-c)) (reach hh) y (sub hy)
      dsimp [w] at h he
      omega
  have hs : (S+range 9) ∪ D ⊆ Ico b (s+9) := by
    intro z hz
    rcases mem_union.mp hz with h | h
    · obtain ⟨y,hy,i,hi,rfl⟩ := mem_add.mp h
      have hi' := mem_range.mp hi
      obtain ⟨h1,h2⟩ := bounds y hy
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨p,hp,hpJ⟩ := mem_biUnion.mp h
      have h2 := (mem_filter.mp hp).2
      obtain ⟨hl,hr⟩ := mem_Ico.mp hpJ
      exact mem_Ico.mpr ⟨by omega,by omega⟩
  have hcard := card_le_card hs
  have jsize (p : ℕ) : (J p).card=2 := by dsimp [J]; rw [Nat.card_Ico]; omega
  rw [card_union_of_disjoint hd,Nat.card_Ico,show D.card=∑ p ∈ G, (J p).card from card_biUnion dJ] at hcard
  simpa [jsize,mul_comm] using hcard


private lemma terminal_counts (T : Finset ℕ) (u : ℕ) (hu : u ∈ T) (hs : u+12 ∈ T) :
    let W := T.filter (fun x => u+12 ≤ x+4)
    (T.filter (· < u)).card + (T.filter (· < u+6)).card + (T.filter (· < u+12)).card +
      2*W.card+2 ≤ 3*T.card := by
  classical
  let W := T.filter (fun x => u+12 ≤ x+4)
  let X := insert u (T.filter (· < u))
  let Y := T.filter (· < u+6)
  have wx : Disjoint X W := by
    apply disjoint_left.mpr
    intro x hx hw
    have dx := (mem_filter.mp hw).2
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · have := (mem_filter.mp hx).2; omega
  have wy : Disjoint Y W := by
    apply disjoint_left.mpr
    intro x hx hw
    have hx' := (mem_filter.mp hx).2
    have hw' := (mem_filter.mp hw).2
    omega
  have xs : X ∪ W ⊆ T := union_subset (insert_subset hu (filter_subset _ _)) (filter_subset _ _)
  have ys : Y ∪ W ⊆ T := union_subset (filter_subset _ _) (filter_subset _ _)
  have cx := card_le_card xs
  have cy := card_le_card ys
  rw [card_union_of_disjoint wx,show X.card=(T.filter (· < u)).card+1 from
    card_insert_of_notMem (by simp)] at cx
  rw [card_union_of_disjoint wy] at cy
  have cs : (T.filter (· < u+12)).card < T.card :=
    card_lt_card (filter_ssubset.mpr ⟨u+12,hs,by omega⟩)
  change _ + Y.card + _ + 2*W.card+2 ≤ 3*T.card
  omega

private lemma case_six (T : Finset ℕ) (u : ℕ) (h6 : 6 ∈ T) (hu : u ∈ T) (hs : u+12 ∈ T)
    (bounds : ∀ x ∈ T, 6 ≤ x ∧ x ≤ u+12)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (gap : ∀ x ∈ T, x+4 < 12 ∨ 14 < x)
    (dense : ∃ z : ℕ, 3 < (T.filter (fun x => z ≤ x ∧ x < z+9)).card) :
    (T.filter (· < u)).card + (T.filter (· < u+6)).card + (T.filter (· < u+12)).card < u+6 := by
  classical
  let s := u+12
  let J := fun p => T.filter (fun x => p ≤ x ∧ x ≤ p+4)
  let B := T.filter (fun p => 4 ≤ (J p).card)
  have hdif (x : ℕ) (hx : x ∈ T) (y : ℕ) (hy : y ∈ T) : y < x+5 ∨ x+8 < y := by
    have h := sep x hx 6 h6 y hy
    omega
  obtain ⟨z,hz⟩ := dense
  let P := T.filter (fun x => z ≤ x ∧ x < z+9)
  change 3 < P.card at hz
  have hne : P.Nonempty := card_pos.mp (by omega)
  let v := P.min' hne
  have hv : v ∈ P := P.min'_mem _
  obtain ⟨hvT,hvz,_⟩ := mem_filter.mp hv
  have subP : P ⊆ J v := by
    intro x hx
    have vx : v ≤ x := P.min'_le x hx
    obtain ⟨hxT,_,hxr⟩ := mem_filter.mp hx
    have dh := hdif v hvT x hxT
    exact mem_filter.mpr ⟨hxT,vx,by omega⟩
  have hvB : v ∈ B := mem_filter.mpr ⟨hvT,hz.trans_le (card_le_card subP)⟩
  let b := B.min' ⟨v,hvB⟩
  have hbB : b ∈ B := B.min'_mem _
  obtain ⟨hbT,hb4⟩ := mem_filter.mp hbB
  have first (p : ℕ) (hp : p ∈ T) (hj : 4 ≤ (J p).card) : b ≤ p :=
    B.min'_le p (mem_filter.mpr ⟨hp,hj⟩)
  obtain ⟨c,hcJ,hbc⟩ : ∃ c ∈ J b, b+3 ≤ c := by
    by_contra! h
    have sub : J b ⊆ Icc b (b+2) := fun x hx => mem_Icc.mpr ⟨(mem_filter.mp hx).2.1,by have := h x hx; omega⟩
    have le := card_le_card sub
    rw [Nat.card_Icc] at le
    omega
  obtain ⟨hcT,_,hcb⟩ := mem_filter.mp hcJ
  let A := T.filter (· < b)
  let S := T.filter (b ≤ ·)
  let W := T.filter (fun x => s ≤ x+4)
  let W' := S.filter (fun x => s ≤ x+4)
  have subST : S ⊆ T := filter_subset _ _
  have bds (x : ℕ) (hx : x ∈ S) : b ≤ x ∧ x ≤ s := ⟨(mem_filter.mp hx).2,(bounds x (subST hx)).2⟩
  have bmax : b ≤ s := (bounds b hbT).2
  have hsS : s ∈ S := mem_filter.mpr ⟨hs,bmax⟩
  have split : A.card+S.card=T.card := by
    simpa only [A,S,not_lt] using card_filter_add_card_filter_not (s:=T) (fun x => x<b)
  obtain ⟨hb15,early⟩ := initial_cost T b hbT (fun x hx => (bounds x hx).1) gap hdif hb4 first
    (fun E hET => (buffer_count E (fun x hx y hy => hdif x (hET hx) y (hET hy))).2)
  change 11*A.card+23 ≤ 3*b at early
  let F := S.filter (fun p => Icc p (p+4) ⊆ S)
  let V := S+range 9
  have full (p : ℕ) (hp : p ∈ F) : Icc p (p+4) ⊆ T := (mem_filter.mp hp).2.trans subST
  have late := late_runs T F s b bmax (fun x hx => (bounds x hx).2) hdif full
  have slots := spare_positions T S F s b c subST hbT hcT hbc hcb full bds hdif sep
  change V.card + 2*(F.filter (fun p => b+p ≤ s)).card ≤ s+9-b at slots
  have cuts := card_filter_add_card_filter_not (s:=F) (fun p => b+p ≤ s)
  simp only [not_le] at cuts
  have cost := (buffer_count S (fun x hx y hy => hdif x (subST hx) y (subST hy))).1
    s hsS (fun x hx => (bds x hx).2)
  change 3*S.card+8 ≤ V.card+2*F.card+2*W'.card at cost
  have wt : W'.card ≤ W.card := card_le_card (fun x hx =>
    mem_filter.mpr ⟨subST (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩)
  have finalCounts := terminal_counts T u hu hs
  change _ + _ + _ + 2*W.card+2 ≤ 3*T.card at finalCounts
  have budget : 3*A.card+2*(F.filter (fun p => s < b+p)).card+6 ≤ b := by omega
  have es : s=u+12 := rfl
  omega


theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1.H2 := by
  exact case_six

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H2

section FoldGR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1

/- A surviving configuration admits a short discrepancy-maximizing interval
strictly between twice the minimum and the middle threshold. Its two endpoints
and two doubled prefix bounds are available. Based on Franchi, Gowers and
Yip, arXiv:2607.06073, section 4. Lean proof by @Deldor14. -/

namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1

open Finset

/-- Excluding early and late maximum-discrepancy intervals. -/
def H1 : Prop := ∀ (T : Finset ℕ) (a u : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    2*a < u → 1 < a → (∀ x ∈ T, a ≤ x) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    ((T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a) ∨ ∃ L w : ℕ, 2*a < L ∧ L+w < u+a ∧ 0 < w ∧ w < a ∧
      L ∈ T ∧ L+w-1 ∈ T ∧ (∀ s n : ℕ, s+n ≤ u+2*a →
        2*(T.filter (fun x => s ≤ x ∧ x < s+n)).card+w ≤
        2*(T.filter (fun x => L ≤ x ∧ x < L+w)).card+n) ∧
      (∀ z : ℕ, z ≤ u+2*a → L+z ∈ T →
        2*(T.filter (· < z)).card + (T.filter (· < L+z)).card ≤ z+(T.filter (· < L)).card) ∧
      3*(T.filter (· < L+w-a)).card ≤ L+w-2*a

/-- The remaining short interior maximum and its prefix bounds. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a u : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ i ∈ T, a ≤ i ∧ i ≤ u+2*a) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    7 ≤ a → u+a+1 < 3*T.card → (∀ x ∈ T, x+4 < 2*a ∨ 2*a+2 < x) →
    (∀ d e : ℕ, e ≤ a → d+e < 2*a →
      (∀ x ∈ T, x ≤ u → x+d ∉ T) → (∀ x ∈ T, x < u+a → x+e ∉ T) →
        ∃ x ∈ T, x ≤ u ∧ x+(d+e) ∈ T) →
    2*a < u → (T.filter (· < (2*a))).card+3 ≤ (T.filter (· < u)).card →
    (∀ v : ℕ, a ≤ v → (T.filter (· < u)).card ≤ (T.filter (· < (v+1))).card+1 → ¬ (∀ d : ℕ, a < d → d ≤ v+2 → ∃ z ∈ T, z ≤ d+1 ∧ d ≤ z+2)) →
    (∀ h : ℕ, 0 < h → h ≤ a → ∃ t : ℕ, a ≤ t ∧ t+3*h ≤ u+2*a+1 ∧
      h < (T.filter (fun x => t ≤ x ∧ x < t+3*h)).card) →
    (∀ z ∈ T, ∀ d : ℕ, d < 2*a → u+2*a ≤ z+d+2 → z+d ≤ u+2*a+3 →
      ∃ x ∈ T, x ≤ u ∧ x+d ∈ T) →
    ∀ L w : ℕ, 2*a < L → L+w < u+a → 0 < w → w < a → L ∈ T → L+w-1 ∈ T →
    (∀ s n : ℕ, s+n ≤ u+2*a →
        2*(T.filter (fun x => s ≤ x ∧ x < s+n)).card+w ≤
        2*(T.filter (fun x => L ≤ x ∧ x < L+w)).card+n) →
    (∀ z : ℕ, z ≤ u+2*a → L+z ∈ T →
        2*(T.filter (· < z)).card + (T.filter (· < L+z)).card ≤ z+(T.filter (· < L)).card) →
    3*(T.filter (· < L+w-a)).card ≤ L+w-2*a →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

theorem main : H1 → H2 → OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1.H3 := by
  intro maximum tail T a u ha hu hu2 bounds sep ha7 dense gap offsets wide many gaps crowded forced
  rcases maximum T a u ha hu hu2 wide (by omega) (fun x hx => (bounds x hx).1) sep with solved | info
  · exact solved
  obtain ⟨L,w,hl,hr,hw,hwa,hL,hR,hmax,hd,hf⟩ := info
  exact tail T a u ha hu hu2 bounds sep ha7 dense gap offsets wide many gaps crowded forced
    L w hl hr hw hwa hL hR hmax hd hf

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1

end FoldGR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H1

/- Discrete discrepancy estimates of Franchi–Gowers–Yip, section 4, arXiv:2607.06073.
Original Lean formalization by @Deldor14. -/
namespace GreenThreeDiscrepancy

open Finset

def window (T : Finset ℕ) (l w : ℕ) := T.filter (fun x => l ≤ x ∧ x < l+w)

def disc (T : Finset ℕ) (l w : ℕ) : ℤ := 2*((window T l w).card:ℤ) - w

private theorem card_split (T : Finset ℕ) (l p q : ℕ) :
    (window T l (p+q)).card = (window T l p).card + (window T (l+p) q).card := by
  classical
  have split : window T l (p+q) = window T l p ∪ window T (l+p) q := by
    ext x
    simp only [window,mem_filter,mem_union]
    constructor
    · rintro ⟨h,lo,hi⟩
      by_cases test : x < l+p
      · exact Or.inl ⟨h,lo,test⟩
      · exact Or.inr ⟨h,by omega,by omega⟩
    · rintro (⟨h,lo,hi⟩ | ⟨h,lo,hi⟩) <;> exact ⟨h,by omega,by omega⟩
  have dis : Disjoint (window T l p) (window T (l+p) q) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨_,_,hi⟩ := mem_filter.mp hx
    obtain ⟨_,lo,_⟩ := mem_filter.mp hy
    omega
  rw [split,card_union_of_disjoint dis]

private theorem paired (T : Finset ℕ) (h l w : ℕ)
    (noPair : ∀ x ∈ T, x+h ∉ T) :
    (window T l w).card + (window T (l+h) w).card ≤ w := by
  let A := (window T l w).image (·+h)
  let B := window T (l+h) w
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact noPair x (mem_filter.mp hx).1 (mem_filter.mp hb).1
  have sub : A ∪ B ⊆ Ico (l+h) (l+h+w) := by
    intro z hz
    rcases mem_union.mp hz with hA | hB
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hA
      obtain ⟨_,lo,hi⟩ := mem_filter.mp hx
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · exact mem_Ico.mpr (mem_filter.mp hB).2
  have b := card_le_card sub
  rw [card_union_of_disjoint dis,Nat.card_Ico] at b
  have c : A.card = (window T l w).card := card_image_of_injective _ (add_left_injective h)
  rw [c] at b
  dsimp [B] at b
  omega

theorem shorten {T : Finset ℕ} {h l n : ℕ} (pos : 0 < h) (long : h < n)
    (noPair : ∀ x ∈ T, x+h ∉ T) :
    ∃ l' n', l ≤ l' ∧ l'+n' ≤ l+n ∧ n' < n ∧ disc T l n ≤ disc T l' n' := by
  by_cases twice : 2*h ≤ n
  · let rest := n-(h+h)
    have len : n = (h+h)+rest := by dsimp [rest]; omega
    have first := card_split T l h h
    have splits := card_split T l (h+h) rest
    rw [←len] at splits
    have bound := paired T h l h noPair
    refine ⟨l+(h+h),rest,by omega,by omega,by omega,?_⟩
    unfold disc
    omega
  · let w := n-h
    let m := h-w
    have hp : 0 < w := by dsimp [w]; omega
    have hm : w+m = h := by dsimp [w,m]; omega
    have hn : n = h+w := by dsimp [w]; omega
    have left := card_split T l w m
    rw [hm] at left
    have right := card_split T l h w
    rw [←hn] at right
    have bound := paired T h l w noPair
    refine ⟨l+w,m,by omega,by omega,by omega,?_⟩
    unfold disc
    omega

theorem short_subinterval {T : Finset ℕ} {h : ℕ} (pos : 0 < h)
    (noPair : ∀ x ∈ T, x+h ∉ T) (l n : ℕ) :
    ∃ l' n', l ≤ l' ∧ l'+n' ≤ l+n ∧ n' ≤ h ∧ disc T l n ≤ disc T l' n' := by
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases short : n ≤ h
    · exact ⟨l,n,le_rfl,le_rfl,short,le_rfl⟩
    obtain ⟨s,m,low,high,lt,d⟩ := shorten pos (Nat.lt_of_not_ge short) noPair (l := l)
    obtain ⟨r,k,lo,hi,small,enough⟩ := ih m lt s
    exact ⟨r,k,low.trans lo,hi.trans high,small,d.trans enough⟩

private theorem disc_split (T : Finset ℕ) (l p q : ℕ) :
    disc T l (p+q) = disc T l p + disc T (l+p) q := by
  simp only [disc,card_split,Nat.cast_add]
  ring

/-- Maximum discrepancy among the half-open integer intervals in [0,U). -/
def Maximizes (T : Finset ℕ) (L w U : ℕ) : Prop :=
  L+w ≤ U ∧ ∀ s n : ℕ, s+n ≤ U → disc T s n ≤ disc T L w

theorem balanced_ends {T : Finset ℕ} {L w U : ℕ} (maximal : Maximizes T L w U)
    (k : ℕ) (kw : k ≤ w) : 0 ≤ disc T L k ∧ 0 ≤ disc T (L+(w-k)) k := by
  obtain ⟨inside,bound⟩ := maximal
  have e1 : k+(w-k)=w := by omega
  have e2 : w-k+k=w := by omega
  have e := disc_split T L k (w-k)
  have f := disc_split T L (w-k) k
  rw [e1] at e
  rw [e2] at f
  have b := bound (L+k) (w-k) (by omega)
  have c := bound L (w-k) (by omega)
  omega

private theorem mirror_pair {T : Finset ℕ} {l m n : ℕ}
    (forbid : ∀ x ∈ T, ∀ y ∈ T, x+y+1 ≠ l+m+n) :
    disc T l n + disc T m n ≤ 0 := by
  let f (x : ℕ) := l+m+n-1-x
  let A := (window T l n).image f
  let B := window T m n
  have inj : A.card = (window T l n).card := by
    apply card_image_of_injOn
    intro x hx y hy e
    obtain ⟨_,xl,xu⟩ := mem_filter.mp hx
    obtain ⟨_,yl,yu⟩ := mem_filter.mp hy
    dsimp [f] at e
    omega
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨xt,xl,xu⟩ := mem_filter.mp hx
    have yt := (mem_filter.mp hb).1
    apply forbid x xt _ yt
    dsimp [f]
    omega
  have sub : A ∪ B ⊆ Ico m (m+n) := by
    intro z hz
    rcases mem_union.mp hz with ha | hb
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      obtain ⟨_,xl,xu⟩ := mem_filter.mp hx
      dsimp [f]
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · exact mem_Ico.mpr (mem_filter.mp hb).2
  have card := card_le_card sub
  rw [card_union_of_disjoint dis,inj,Nat.card_Ico] at card
  dsimp [B] at card
  unfold disc
  omega

/-- Discrete version of the left-endpoint condition in FGY Lemma 4.2.
At a point z with L+z in T, no suffix ending at z has positive discrepancy. -/
theorem suffix_nonpositive_of_sum {T : Finset ℕ} {L w U z : ℕ}
    (maximal : Maximizes T L w U) (endBound : z ≤ U) (anchor : L+z ∈ T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (s k : ℕ) (ends : s+k = z) : disc T s k ≤ 0 := by
  have avoid (q n : ℕ) (eq : q+n=z) : disc T L n + disc T q n ≤ 0 := by
    apply mirror_pair
    intro x hx y hy bad
    have h := sep x hx y hy _ anchor
    omega
  by_cases small : k ≤ w
  · have left := (balanced_ends maximal k small).1
    have pair := avoid s k ends
    omega
  · have len : k-w+w=k := by omega
    have split := disc_split T s (k-w) w
    rw [len] at split
    have first := maximal.2 s (k-w) (by omega)
    have last := avoid (s+(k-w)) w (by omega)
    omega

/-- Discrete version of the right-endpoint difference condition in FGY
Lemma 4.2. The argument also works when the difference itself is forbidden
without belonging to T. -/
theorem suffix_nonpositive_of_difference {T : Finset ℕ} {L w U z : ℕ}
    (maximal : Maximizes T L w U) (endBound : z ≤ U) (ordered : z ≤ L+w)
    (absent : ∀ x ∈ T, x+(L+w-z) ∉ T)
    (s k : ℕ) (ends : s+k=z) : disc T s k ≤ 0 := by
  let h := L+w-z
  have pair (q n : ℕ) : disc T q n + disc T (q+h) n ≤ 0 := by
    have b := paired T h q n absent
    unfold disc
    omega
  by_cases small : k ≤ w
  · have eq : s+h = L+(w-k) := by dsimp [h]; omega
    have b := pair s k
    rw [eq] at b
    have right := (balanced_ends maximal k small).2
    omega
  · have len : k-w+w=k := by omega
    have split := disc_split T s (k-w) w
    rw [len] at split
    have first := maximal.2 s (k-w) (by omega)
    have eq : s+(k-w)+h = L := by dsimp [h]; omega
    have last := pair (s+(k-w)) w
    rw [eq] at last
    omega

private theorem one_cell (T : Finset ℕ) (s : ℕ) :
    (window T s 1).card = if s ∈ T then 1 else 0 := by
  classical
  by_cases hs : s ∈ T
  · have eq : window T s 1 = {s} := by
      ext x
      simp only [window,mem_filter,mem_singleton]
      constructor
      · rintro ⟨_,l,r⟩; omega
      · rintro rfl; exact ⟨hs,le_rfl,by omega⟩
    simp [eq,hs]
  · have eq : window T s 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨xt,lo,hi⟩ := mem_filter.mp hx
      have e : x=s := by omega
      exact hs (e ▸ xt)
    simp [eq,hs]

theorem exists_short_maximum {T : Finset ℕ} {h : ℕ} (pos : 0 < h)
    (noPair : ∀ x ∈ T, x+h ∉ T) (U : ℕ) :
    ∃ L w, w ≤ h ∧ Maximizes T L w U := by
  classical
  let W := ((range (U+1)).product (range (U+1))).filter (fun x => x.1+x.2 ≤ U)
  have valid (l n : ℕ) (hn : l+n ≤ U) : (l,n) ∈ W :=
    mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,hn⟩
  obtain ⟨i,hi,best⟩ := exists_max_image W (fun x => disc T x.1 x.2)
    ⟨(0,0),valid 0 0 (by omega)⟩
  have inside := (mem_filter.mp hi).2
  obtain ⟨l,n,left,right,small,atLeast⟩ := short_subinterval pos noPair i.1 i.2
  exact ⟨l,n,small,right.trans inside,fun s k h => (best (s,k) (valid s k h)).trans atLeast⟩

theorem endpoints_mem {T : Finset ℕ} {L w U a : ℕ} (best : Maximizes T L w U)
    (ha : a ∈ T) (haU : a < U) : 0 < w ∧ L ∈ T ∧ L+w-1 ∈ T := by
  have occ := best.2 a 1 (by omega)
  unfold disc at occ
  rw [one_cell,if_pos ha] at occ
  have pos : 0 < w := by
    by_contra! z
    obtain rfl : w=0 := by omega
    have empty : window T L 0 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨_,lo,hi⟩ := mem_filter.mp hx
      omega
    norm_num [empty] at occ
  obtain ⟨left,right⟩ := balanced_ends best 1 pos
  unfold disc at left right
  rw [one_cell] at left right
  by_cases hl : L ∈ T
  · refine ⟨pos,hl,?_⟩
    by_contra miss
    have e : L+(w-1)=L+w-1 := by omega
    rw [e,if_neg miss] at right
    norm_num at right
  · rw [if_neg hl] at left
    norm_num at left

private theorem doubled_marked {T A : Finset ℕ} {L U : ℕ}
    (marks : ∀ x, L+x ∈ A → x ≤ U →
      x ∉ T ∧ ∀ t k, t+k=x → disc T t k ≤ 0)
    (s n : ℕ) (inside : s+n ≤ U)
    (goodEnd : ∀ t k : ℕ, t+k=s+n → disc T t k ≤ 0) :
    2*(window T s n).card + (window A (L+s) n).card ≤ n := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases empty : window A (L+s) n = ∅
    · have b := goodEnd s n rfl
      unfold disc at b
      rw [empty,card_empty]
      omega
    obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨xt,xl,xr⟩ := mem_filter.mp hx
    let k := x-(L+s)
    let m := n-k-1
    have eq : x = L+(s+k) := by dsimp [k]; omega
    have kn : k<n := by dsimp [k]; omega
    have endEq : k+(1+m)=n := by dsimp [m]; omega
    have hit : L+(s+k) ∈ A := eq ▸ xt
    obtain ⟨miss,reset⟩ := marks (s+k) hit (by omega)
    have first := ih k kn s (by omega) reset
    have second := ih m (by omega) (s+k+1) (by omega)
      (fun t len ends => goodEnd t len (by omega))
    have share (P : Finset ℕ) (z : ℕ) :
        (window P z n).card = (window P z k).card + (window P (z+k) 1).card +
          (window P (z+k+1) m).card := by
      have a := card_split P z k (1+m)
      have b := card_split P (z+k) 1 m
      rw [endEq,b] at a
      omega
    have low := share T s
    have high := share A (L+s)
    rw [one_cell,if_neg miss] at low
    have sumEq : L+s+k=L+(s+k) := by omega
    have sumEq' : L+(s+k)+1=L+(s+k+1) := by omega
    rw [one_cell,sumEq,sumEq',if_pos hit] at high
    omega

/-- A counting version of the zero endpoint-discrepancy case of FGY 4.3.
The original interval contributes twice its cardinality. An occupied
translated position splits the interval into two smaller instances. -/
theorem doubled_window {T : Finset ℕ} {L w U : ℕ}
    (best : Maximizes T L w U) (hL : L ∈ T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) (s n : ℕ)
    (inside : s+n ≤ U) (goodEnd : ∀ t k : ℕ, t+k=s+n → disc T t k ≤ 0) :
    2*(window T s n).card + (window T (L+s) n).card ≤ n := by
  apply doubled_marked _ s n inside goodEnd
  intro x hit bound
  refine ⟨?_,suffix_nonpositive_of_sum best bound hit sep⟩
  intro hx
  have h := sep L hL x hx (L+x) hit
  omega

private theorem window_zero (T : Finset ℕ) (n : ℕ) : window T 0 n = T.filter (· < n) := by
  ext x
  simp [window]

/-- At any occupied translate of the left endpoint of a maximizing interval,
a doubled prefix and the following translated window occupy at most z places. -/
theorem anchor_density {T : Finset ℕ} {L w U z : ℕ} (best : Maximizes T L w U)
    (hL : L ∈ T) (hz : z ≤ U) (hit : L+z ∈ T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    2*(T.filter (· < z)).card + (T.filter (· < L+z)).card ≤ z+(T.filter (· < L)).card := by
  have both := doubled_window best hL sep 0 z (by omega)
    (fun t k e => suffix_nonpositive_of_sum best hz hit sep t k (by omega))
  have part := card_split T 0 L z
  simp only [Nat.zero_add,Nat.add_zero,window_zero] at both part
  omega

/-- If a maximizing interval starts at the minimum, the double-hit case of
the three-prefix bound follows from §4.3. The endpoint u supplies strictness. -/
theorem residual_of_maximum_at_minimum {T : Finset ℕ} {a u w : ℕ}
    (best : Maximizes T a w (u+2*a+1)) (ha : a ∈ T) (amin : ∀x∈T, a ≤ x)
    (hu : u ∈ T) (hU : u+2*a ∈ T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a := by
  have apos : 0 < a := by have h := sep a ha a ha a ha; omega
  have e : a+(u+a)=u+2*a := by omega
  have density := anchor_density (z := u+a) best ha (by omega) (e.symm ▸ hU) sep
  rw [e] at density
  have empty : T.filter (· < a) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨xt,xa⟩ := mem_filter.mp hx
    exact (amin x xt).not_gt xa
  rw [empty,card_empty] at density
  have sub : insert u (T.filter (· < u)) ⊆ T.filter (· < u+a) := by
    intro x hx
    obtain rfl | hx := mem_insert.mp hx
    · exact mem_filter.mpr ⟨hu,by omega⟩
    · obtain ⟨xt,xu⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨xt,by omega⟩
  have strict := card_le_card sub
  rw [card_insert_of_notMem (by simp)] at strict
  omega

/-- The difference-set part of FGY 4.3, combined with sum-freeness, for
the prefix reflected about the right end of the maximizing interval. -/
theorem reflected_prefix {T : Finset ℕ} {L w U a : ℕ} (best : Maximizes T L w U)
    (ha : a ∈ T) (amin : ∀x∈T, a ≤ x) (endpoint : L+w-1 ∈ T)
    (two : 2*a≤L+w)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    3*(T.filter (· < L+w-a)).card ≤ L+w-2*a := by
  let n := L+w-2*a
  let f (x : ℕ) := L+w-1-x
  let P := window T a n
  let A := P.image f
  have apos : 0 < a := by have h := sep a ha a ha a ha; omega
  have len : a+n=L+w-a := by dsimp [n]; omega
  have bound : L+w ≤ U := best.1
  have Pcard : P = T.filter (· < L+w-a) := by
    ext x
    simp only [P,window,mem_filter,len]
    constructor
    · rintro ⟨xt,_,hi⟩; exact ⟨xt,hi⟩
    · rintro ⟨xt,hi⟩; exact ⟨xt,amin x xt,hi⟩
  have cardA : A.card = P.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    obtain ⟨_,xl,xh⟩ := mem_filter.mp hx
    obtain ⟨_,yl,yh⟩ := mem_filter.mp hy
    dsimp [f] at e
    omega
  have allA : window A a n = A := by
    ext x
    simp only [window,mem_filter,and_iff_left_iff_imp]
    intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨_,yl,yh⟩ := mem_filter.mp hy
    dsimp [f]
    exact ⟨by omega,by omega⟩
  have forbidden (h : ℕ) (hm : h ∈ T) (d : ℕ) (diff : h ≤ d ∧ d ≤ h+1) :
      ∀x∈T, x+d ∉ T := by
    intro x hx hit
    have b := sep x hx h hm (x+d) hit
    omega
  have last : ∀ t k, t+k=a+n → disc T t k ≤ 0 := by
    intro t k e
    apply suffix_nonpositive_of_difference best (by omega) (by omega) _ t k e
    apply forbidden a ha
    omega
  have total := doubled_marked (T := T) (A := A) (L := 0) (U := U)
    (by
      intro x mark hU
      rw [Nat.zero_add] at mark
      obtain ⟨y,hy,hxy⟩ := mem_image.mp mark
      obtain ⟨yt,yl,yh⟩ := mem_filter.mp hy
      dsimp [f] at hxy
      refine ⟨?_,suffix_nonpositive_of_difference best hU (by omega) (forbidden y yt _ (by omega))⟩
      intro xt
      have b := sep x xt y yt (L+w-1) endpoint
      omega) a n (by omega) last
  rw [Nat.zero_add,allA,cardA] at total
  change 2*P.card+P.card ≤ n at total
  rw [Pcard] at total
  omega

private theorem prefix_split (T : Finset ℕ) (l r : ℕ) (lr : l≤r) :
    (T.filter (· < r)).card = (T.filter (· < l)).card + (window T l (r-l)).card := by
  have h := card_split T 0 l (r-l)
  rw [show l+(r-l)=r by omega] at h
  simpa only [Nat.zero_add,window_zero] using h

private theorem prefix_growth (T : Finset ℕ) (l r : ℕ) (lr : l≤r) :
    (T.filter (· < r)).card ≤ (T.filter (· < l)).card + (r-l) := by
  have sub : window T l (r-l) ⊆ Ico l r := by
    intro x hx
    obtain ⟨_,lo,hi⟩ := mem_filter.mp hx
    exact mem_Ico.mpr ⟨lo,by omega⟩
  have h := card_le_card sub
  rw [Nat.card_Ico] at h
  have split := prefix_split T l r lr
  omega

/-- A discrepancy maximum reaching the central prefix settles the double-hit
case. The reflected prefix gives a third copy of the same count, as in FGY 4.7. -/
theorem residual_of_late_maximum {T : Finset ℕ} {a u L w : ℕ}
    (best : Maximizes T L w (u+2*a)) (ha : a ∈ T) (amin : ∀x∈T, a ≤ x)
    (hu : u ∈ T) (late : u+a ≤ L+w)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a := by
  let z := L+w-a
  have apos : 0<a := by have h := sep a ha a ha a ha; omega
  have au := amin u hu
  have inside := best.1
  have uz : u≤z := by dsimp [z]; omega
  have zx : z≤u+a := by dsimp [z]; omega
  have zU : z ≤ u+2*a := by omega
  have endpoint := (endpoints_mem best ha (by omega)).2.2
  have triple := reflected_prefix best ha amin endpoint (by omega) sep
  change 3*(T.filter (· < z)).card ≤ L+w-2*a at triple
  have forbidden : ∀x∈T, x+a ∉ T := by
    intro x hx ht
    have b := sep x hx a ha (x+a) ht
    omega
  have pairedCard := paired T a z a forbidden
  have both := card_split T z a a
  have cover : window T z (u+2*a-z) ⊆ window T z (a+a) := by
    intro x hx
    obtain ⟨xt,lo,hi⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨xt,lo,by omega⟩
  have covers := card_le_card cover
  have pU := prefix_split T z (u+2*a) zU
  have terminal : (T.filter (· < u+2*a)).card ≤ (T.filter (· < z)).card + a := by omega
  have centre := prefix_growth T z (u+a) zx
  by_cases h : u < z
  · have sub : insert u (T.filter (· < u)) ⊆ T.filter (· < z) := by
      intro x hx
      obtain rfl | hx := mem_insert.mp hx
      · exact mem_filter.mpr ⟨hu,h⟩
      · obtain ⟨xt,lo⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨xt,by omega⟩
    have strict := card_le_card sub
    rw [card_insert_of_notMem (by simp)] at strict
    dsimp [z] at *
    omega
  · have e : z=u := by omega
    have miss : u+a-1 ∉ T := by
      intro ht
      have b := sep u hu a ha (u+a-1) ht
      omega
    have eq : T.filter (· < u+a) = T.filter (· < u+a-1) := by
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨xt,lo⟩
        refine ⟨xt,?_⟩
        by_contra! no
        have b : x=u+a-1 := by omega
        exact miss (b ▸ xt)
      · rintro ⟨xt,lo⟩; exact ⟨xt,by omega⟩
    have growth := prefix_growth T z (u+a-1) (by omega)
    rw [← eq,e] at growth
    rw [e] at terminal triple
    dsimp [z] at e
    omega

/-- A maximizing interval cannot begin in the first two minimum-length
blocks of a counterexample. This is the discrete reflected count in FGY §4.6. -/
theorem residual_of_early_maximum {T : Finset ℕ} {a u L w : ℕ}
    (best : Maximizes T L w (u+2*a)) (ha : a ∈ T) (amin : ∀x∈T, a ≤ x)
    (hu : u ∈ T) (hU : u+2*a ∈ T) (far : 2*a≤u) (early : L≤2*a)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a := by
  let y := u+2*a-L
  have apos : 0<a := by have h := sep a ha a ha a ha; omega
  have occupied := (endpoints_mem best ha (by omega)).2.1
  have aL := amin L occupied
  have inside := best.1
  have before : L<2*a := by
    have h := sep a ha a ha L occupied
    omega
  have uy : u<y := by dsimp [y]; omega
  have yx : y≤u+a := by dsimp [y]; omega
  have Ly : L≤y := by omega
  have ydef : L+y = u+2*a := by dsimp [y]; omega
  have empty : T.filter (· < a) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨xt,lo⟩ := mem_filter.mp hx
    exact (amin x xt).not_gt lo
  have initial := prefix_split T a L aL
  rw [empty,card_empty,zero_add] at initial
  have pre := disc_split T a (L-a) w
  rw [show a+(L-a)=L by omega] at pre
  have extBound := best.2 a (L-a+w) (by omega)
  have balance : disc T a (L-a) ≤ 0 := by omega
  unfold disc at balance
  have free (x : ℕ) (hx : x ∈ T) : x+a ∉ T := by
    intro ht
    have e := sep x hx a ha (x+a) ht
    omega
  have p := paired T a L a free
  have pd := card_split T L a a
  have sub : window T L L ⊆ window T L (a+a) := by
    intro x hx
    obtain ⟨xt,lo,hi⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨xt,lo,by omega⟩
  have cap := card_le_card sub
  have cap' := prefix_split T L (L+L) (by omega)
  rw [show L+L-L=L by omega] at cap'
  have reflection := mirror_pair (T := T) (l := a) (m := y) (n := L-a)
    (by
      intro v hv q hq eq
      have e := sep v hv q hq (u+2*a) hU
      omega)
  unfold disc at reflection
  have reflected := prefix_split T y (u+a) yx
  rw [show u+a-y=L-a by omega] at reflected
  have main := doubled_window best occupied sep L (y-L) (by omega)
    (fun t k ends => suffix_nonpositive_of_sum best (z := y) (by omega) (ydef.symm ▸ hU) sep t k (by omega))
  have first := prefix_split T L y Ly
  have second := prefix_split T (L+L) (u+2*a) (by omega)
  rw [show u+2*a-(L+L)=y-L by omega] at second
  have sub' : insert u (T.filter (· < u)) ⊆ T.filter (· < y) := by
    intro x hx
    obtain rfl | hx := mem_insert.mp hx
    · exact mem_filter.mpr ⟨hu,uy⟩
    · obtain ⟨xt,lo⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨xt,by omega⟩
  have strict := card_le_card sub'
  rw [card_insert_of_notMem (by simp)] at strict
  omega


end GreenThreeDiscrepancy

open GreenThreeDiscrepancy Finset

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1.H1 := by
  classical
  intro T a u ha hu hu2 wide ha2 amin sep
  by_cases sol : (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a
  · exact Or.inl sol
  right
  have forbid (x : ℕ) (hx : x ∈ T) : x+(a-1) ∉ T := by
    intro hit
    have h := sep x hx a ha (x+(a-1)) hit
    omega
  obtain ⟨L,w,hwa,best⟩ := exists_short_maximum (by omega : 0 < a-1) forbid (u+2*a)
  obtain ⟨hw,hL,hR⟩ := endpoints_mem best ha (by omega)
  have hl : 2*a < L := by
    by_contra! early
    exact sol (residual_of_early_maximum best ha amin hu hu2 wide.le early sep)
  have hr : L+w < u+a := by
    by_contra! late
    exact sol (residual_of_late_maximum best ha amin hu late sep)
  refine ⟨L,w,hl,hr,hw,by omega,hL,hR,?_,?_,?_⟩
  · intro s n h
    have v := best.2 s n h
    unfold disc window at v
    omega
  · intro z hz hit
    exact anchor_density best hL hz hit sep
  · exact reflected_prefix best ha amin hR (by omega) sep

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H1

section FoldGR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1

/- Finite equal-discrepancy doubling and the first gap in a possible
counterexample. The arithmetic statements use the two integral offsets
arising from addition of unit cells. Based on Franchi, Gowers and Yip,
arXiv:2607.06073, Theorem 3.12 and Lemmas 4.5–4.9. -/
namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1

open Finset
open scoped Pointwise

open Finset

private theorem image_card {A : Finset ℕ} {M : ℕ} (bound : ∀ x ∈ A,x ≤ M) :
    (A.image (M-·)).card=A.card := by
  apply card_image_of_injOn
  intro x hx y hy e
  have xl := bound x hx; have yl := bound y hy
  change M-x=M-y at e
  omega

private theorem reflected_window {A : Finset ℕ} {M p n : ℕ} (bound : ∀ x ∈ A,x ≤ M) (inside : p+n ≤ M+1) :
    ((A.image (M-·)).filter (fun x => p ≤ x ∧ x<p+n)).card =
      (A.filter (fun x => M+1-(p+n) ≤ x ∧ x<M+1-(p+n)+n)).card := by
  let U := A.filter (fun x => M+1-(p+n) ≤ x ∧ x<M+1-(p+n)+n)
  have eq : (A.image (M-·)).filter (fun x => p ≤ x ∧ x<p+n) = U.image (M-·) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hz
      obtain ⟨x,hx,e⟩ := mem_image.mp hit
      have lim := bound x hx
      change M-x=z at e
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,by omega,by omega⟩,e⟩
    · intro hz
      obtain ⟨x,hx,e⟩ := mem_image.mp hz
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hx
      have lim := bound x hit
      change M-x=z at e
      exact mem_filter.mpr ⟨mem_image.mpr ⟨x,hit,e⟩,by omega,by omega⟩
  rw [eq,image_card (fun x hx => bound x (mem_filter.mp hx).1)]

private theorem clip {A : Finset ℕ} {M : ℕ} (bound : ∀ x ∈ A,x ≤ M) (p n : ℕ) :
    A.filter (fun x => p ≤ x ∧ x<p+n) = A.filter (fun x => p ≤ x ∧ x<p+min n (M+1-p)) := by
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hit,lo,hi⟩
    have lim := bound x hit
    exact ⟨hit,lo,by omega⟩
  · rintro ⟨hit,lo,hi⟩
    exact ⟨hit,lo,by omega⟩

private theorem mirrored {A : Finset ℕ} {M D : ℕ} (bound : ∀ x ∈ A,x ≤ M) (dpos : 0<D)
    (cap : ∀p n : ℕ,2*(A.filter (fun x => p ≤ x ∧ x<p+n)).card ≤ n+D)
    (point : ∃p n : ℕ,n+D ≤ 2*(A.filter (fun x => p ≤ x ∧ x<p+n)).card) :
    (∀p n : ℕ,2*((A.image (M-·)).filter (fun x => p ≤ x ∧ x<p+n)).card ≤ n+D) ∧
    ∃p n : ℕ,n+D ≤ 2*((A.image (M-·)).filter (fun x => p ≤ x ∧ x<p+n)).card := by
  have bound' (x : ℕ) (hx : x ∈ A.image (M-·)) : x ≤ M := by
    obtain ⟨y,_,eq⟩ := mem_image.mp hx
    change M-y=x at eq
    omega
  constructor
  · intro p n
    rw [clip bound' p n]
    by_cases hi : M+1 < p
    · have never (x : ℕ) : ¬ (p ≤ x ∧ x<p) := by omega
      simp [show M+1-p=0 by omega,never]
    rw [reflected_window bound (by omega)]
    have z := cap (M+1-(p+min n (M+1-p))) (min n (M+1-p))
    omega
  · obtain ⟨p,n,rise⟩ := point
    let w := min n (M+1-p)
    have ep := clip bound p n
    rw [ep] at rise
    change n+D ≤ 2*(A.filter (fun x => p ≤ x ∧ x<p+w)).card at rise
    have pos : 0<w := by
      by_contra! nz
      have e : w=0 := by omega
      have never (x : ℕ) : ¬ (p ≤ x ∧ x<p) := by omega
      simp [e,never] at rise
      omega
    have hi : p+w ≤ M+1 := by dsimp [w] at *; omega
    refine ⟨M+1-(p+w),w,?_⟩
    rw [reflected_window bound (by omega),show M+1-(M+1-(p+w)+w)=p by omega]
    have le : w ≤ n := min_le_left _ _
    omega

private theorem maximum_prefix {T : Finset ℕ} {a u L w : ℕ} (al : 0<a) (left : L ∈ T) (loc : L+w<u+a)
    (best : ∀p n : ℕ,p+n≤u+2*a → 2*(T.filter (fun x => p ≤ x ∧ x<p+n)).card+w ≤
      2*(T.filter (fun x => L ≤ x ∧ x<L+w)).card+n) :
    let P := T.filter (· < u+a)
    ∃D : ℕ, 0<D ∧ w+D=2*(T.filter (fun x => L ≤ x ∧ x<L+w)).card ∧
      (∀p n : ℕ,2*(P.filter (fun x => p ≤ x ∧ x<p+n)).card ≤ n+D) ∧
      ∃p n : ℕ,n+D ≤ 2*(P.filter (fun x => p ≤ x ∧ x<p+n)).card := by
  let P := T.filter (· < u+a)
  let q := (T.filter (fun x => L ≤ x ∧ x<L+w)).card
  have one : T.filter (fun x => L ≤ x ∧ x<L+1)={L} := by
    ext x
    simp only [mem_filter,mem_singleton]
    exact ⟨fun ⟨_,lo,hi⟩ => by omega,fun e => ⟨e ▸ left,by omega,by omega⟩⟩
  have single := best L 1 (by omega)
  rw [one,card_singleton] at single
  change 2*1+w ≤ 2*q+1 at single
  let D := 2*q-w
  have disc : w+D=2*q := by dsimp [D]; omega
  have eq (p n : ℕ) (inside : p+n ≤ u+a) :
      P.filter (fun x => p ≤ x ∧ x<p+n)=T.filter (fun x => p ≤ x ∧ x<p+n) := by
    ext x
    simp only [P,mem_filter]
    exact ⟨fun ⟨⟨h,_⟩,lo,hi⟩ => ⟨h,lo,hi⟩,fun ⟨h,lo,hi⟩ => ⟨⟨h,by omega⟩,lo,hi⟩⟩
  have bounds (x : ℕ) (hx : x ∈ P) : x ≤ u+a-1 := by have hi := (mem_filter.mp hx).2; omega
  refine ⟨D,by omega,disc,?_,L,w,?_⟩
  · intro p n
    change 2*(P.filter (fun x => p ≤ x ∧ x<p+n)).card ≤ n+D
    rw [clip bounds p n]
    let r := min n (u+a-1+1-p)
    change 2*(P.filter (fun x => p ≤ x ∧ x<p+r)).card ≤ n+D
    by_cases high : u+a<p
    · have e : r=0 := by dsimp [r]; omega
      have never (x : ℕ) : ¬ (p ≤ x ∧ x<p) := by omega
      simp [e,never]
    have inside : p+r ≤ u+a := by dsimp [r]; omega
    rw [eq p r inside]
    have c := best p r (by omega)
    change 2*(T.filter (fun x => p ≤ x ∧ x<p+r)).card+w ≤ 2*q+r at c
    have rn : r ≤ n := min_le_left _ _
    omega
  · change w+D ≤ 2*(P.filter (fun x => L ≤ x ∧ x<L+w)).card
    rw [eq L w loc.le]
    exact disc.le


/-- The discrete equal-discrepancy sumset theorem. -/
def H1 : Prop := ∀ (A B : Finset ℕ) (D : ℕ), 0 < D →
    (∀ p n : ℕ, 2*(A.filter (fun x => p ≤ x ∧ x<p+n)).card ≤ n+D) →
    (∀ p n : ℕ, 2*(B.filter (fun x => p ≤ x ∧ x<p+n)).card ≤ n+D) →
    (∃ p n : ℕ, n+D ≤ 2*(A.filter (fun x => p ≤ x ∧ x<p+n)).card) →
    (∃ p n : ℕ, n+D ≤ 2*(B.filter (fun x => p ≤ x ∧ x<p+n)).card) →
    2*A.card+2*B.card ≤ ((A+B)+Finset.range 2).card+2*D

/-- Packing positive and negative differences forces a gap of width at
least the minimum around the reflected discrepancy interval. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a u L w D : ℕ), 0 < a → (∀ x ∈ T, a ≤ x) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) → 0 < w → w < a → L ∈ T → L+w-1 ∈ T →
    w+D=2*(T.filter (fun x => L ≤ x ∧ x<L+w)).card →
    (let P := T.filter (· < u+a)
     4*P.card ≤ ((P+P.image (fun x => u+a-x))+Finset.range 2).card+2*D) →
    u+a ≤ (T.filter (· < u)).card+(T.filter (· < u+a)).card+(T.filter (· < u+2*a)).card →
    ((T.filter (· < u)).card+2*(T.filter (· < u+a)).card ≤ u+D) ∧ (∀ t ∈ T, t+L < u+a ∨ u+2*a < t+L+w) ∧ (∀ t ∈ T, ∀ v ∈ T, t+L < u+a → u+a ≤ v+L → t+a ≤ v)

/-- The remaining configuration has its discrepancy interval starting
strictly before the lower outer prefix, with an explicit wide gap. -/
def H3 : Prop := ∀ (T : Finset ℕ) (a u L w D : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ i ∈ T, a ≤ i ∧ i ≤ u+2*a) → (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    7 ≤ a → u+a+1 < 3*T.card → (∀ x ∈ T, x+4 < 2*a ∨ 2*a+2 < x) →
    (∀ d e : ℕ, e ≤ a → d+e < 2*a → (∀ x ∈ T, x ≤ u → x+d ∉ T) →
      (∀ x ∈ T, x < u+a → x+e ∉ T) → ∃ x ∈ T, x ≤ u ∧ x+(d+e) ∈ T) →
    2*a < u → (T.filter (· < (2*a))).card+3 ≤ (T.filter (· < u)).card →
    (∀ v : ℕ, a ≤ v → (T.filter (· < u)).card ≤ (T.filter (· < (v+1))).card+1 → ¬ (∀ d : ℕ, a < d → d ≤ v+2 → ∃ z ∈ T, z ≤ d+1 ∧ d ≤ z+2)) →
    (∀ h : ℕ, 0 < h → h ≤ a → ∃ t : ℕ, a ≤ t ∧ t+3*h ≤ u+2*a+1 ∧
      h < (T.filter (fun x => t ≤ x ∧ x < t+3*h)).card) →
    (∀ z ∈ T, ∀ d : ℕ, d < 2*a → u+2*a ≤ z+d+2 → z+d ≤ u+2*a+3 →
      ∃ x ∈ T, x ≤ u ∧ x+d ∈ T) →
    2*a < L → L < u → L+w < u+a → 0 < w → w < a → L ∈ T → L+w-1 ∈ T →
    (∀ s n : ℕ, s+n ≤ u+2*a → 2*(T.filter (fun x => s ≤ x ∧ x<s+n)).card+w ≤
      2*(T.filter (fun x => L ≤ x ∧ x<L+w)).card+n) →
    (∀ z : ℕ, z ≤ u+2*a → L+z ∈ T → 2*(T.filter (· < z)).card+
      (T.filter (· < L+z)).card ≤ z+(T.filter (· < L)).card) →
    3*(T.filter (· < L+w-a)).card ≤ L+w-2*a →
    0 < D → w+D=2*(T.filter (fun x => L ≤ x ∧ x<L+w)).card → (T.filter (· < u)).card+2*(T.filter (· < u+a)).card ≤ u+D →
    (∀ t ∈ T, t+L < u+a ∨ u+2*a < t+L+w) → (∀ t ∈ T, ∀ v ∈ T, t+L < u+a → u+a ≤ v+L → t+a ≤ v) →
    (T.filter (· < u)).card+(T.filter (· < u+a)).card+
      (T.filter (· < u+2*a)).card < u+a

theorem main : H1 → H2 → H3 → OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1.H2 := by
  intro doubling extract remaining T a u ha hu hu2 bounds separate ha7 dense initial offsets
    wide0 many gaps crowded forced L w hl hr hw haW hL hR best anchor reflected
  by_contra! failed
  let P := T.filter (· < u+a)
  have bounded (x : ℕ) (hx : x ∈ P) : x ≤ u+a := (mem_filter.mp hx).2.le
  obtain ⟨D,pos,eq,cap,point⟩ := maximum_prefix (by omega : 0<a) hL hr best
  obtain ⟨cb,pb⟩ := mirrored (M:=u+a) bounded pos cap point
  have sd := doubling P (P.image (fun x => u+a-x)) D pos cap cb point pb
  rw [image_card bounded] at sd
  have bd : 4*P.card ≤ ((P+P.image (fun x => u+a-x))+range 2).card+2*D := by omega
  obtain ⟨hm,gap,wide⟩ := extract T a u L w D (by omega) (fun x hx => (bounds x hx).1)
    separate hw haW hL hR eq bd failed
  have before : L<u := by
    have g := gap a ha
    omega
  have solved := remaining T a u L w D ha hu hu2 bounds separate ha7 dense initial offsets
    wide0 many gaps crowded forced hl before hr hw haW hL hR best anchor reflected pos eq hm gap wide
  omega

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1

end FoldGR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H1

/- Original integer-cell proof by @Deldor14, based on the mathematical
arguments of Franchi, Gowers and Yip, arXiv:2607.06073. -/

namespace GreenFGY

open Finset
open scoped Pointwise

def count (A : Finset ℕ) (n : ℕ) := (A.filter (· < n)).card
def half (A : Finset ℕ) := A.image (2*·) ∪ A.image (fun i => 2*i+1)

theorem mem_half {A : Finset ℕ} {z : ℕ} :
    z ∈ half A ↔ ∃ x ∈ A, z=2*x ∨ z=2*x+1 := by
  simp only [half,mem_union,mem_image]
  constructor
  · rintro (⟨x,hx,h⟩ | ⟨x,hx,h⟩)
    · exact ⟨x,hx,Or.inl h.symm⟩
    · exact ⟨x,hx,Or.inr h.symm⟩
  · rintro ⟨x,hx,h | h⟩
    · exact Or.inl ⟨x,hx,h.symm⟩
    · exact Or.inr ⟨x,hx,h.symm⟩

private theorem half_count (A : Finset ℕ) (n e : ℕ) (he : e ≤ 1) :
    count (half A) (2*n+e) = count A (n+e) + count A n := by
  let P := (A.filter (· < n+e)).image (2*·)
  let Q := (A.filter (· < n)).image (fun i => 2*i+1)
  have eq : (half A).filter (· < 2*n+e) = P ∪ Q := by
    ext z
    simp only [mem_filter,mem_half,P,Q,mem_union,mem_image]
    constructor
    · rintro ⟨⟨x,hx,h | h⟩,hl⟩
      · exact Or.inl ⟨x,⟨hx,by omega⟩,h.symm⟩
      · exact Or.inr ⟨x,⟨hx,by omega⟩,h.symm⟩
    · rintro (⟨x,⟨hx,hl⟩,h⟩ | ⟨x,⟨hx,hl⟩,h⟩)
      · exact ⟨⟨x,hx,Or.inl h.symm⟩,by omega⟩
      · exact ⟨⟨x,hx,Or.inr h.symm⟩,by omega⟩
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z hz hq
    obtain ⟨x,_,h1⟩ := mem_image.mp hz
    obtain ⟨y,_,h2⟩ := mem_image.mp hq
    omega
  have cp : P.card = count A (n+e) := card_image_of_injective _ (by intro x y h; dsimp at h; omega)
  have cq : Q.card = count A n := card_image_of_injective _ (by intro x y h; dsimp at h; omega)
  unfold count
  rw [eq,card_union_of_disjoint dis,cp,cq]
  rfl

private theorem reflect_before (A B : Finset ℕ) {n q : ℕ} (hq : q ≤ n)
    (noAdd : ∀ x ∈ A, ∀ y ∈ B, x+y+1 ≠ n) :
    count A q + count B n ≤ q+count B (n-q) := by
  let P := A.filter (· < q)
  let U := B.filter (fun y => n-q ≤ y ∧ y < n)
  let Q := U.image (fun y => n-1-y)
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro x hx hxQ
    obtain ⟨y,hy,he⟩ := mem_image.mp hxQ
    obtain ⟨hyB,yl,yr⟩ := mem_filter.mp hy
    exact noAdd x (mem_filter.mp hx).1 y hyB (by omega)
  have sub : P ∪ Q ⊆ range q := by
    intro x hx
    rcases mem_union.mp hx with hp | hQ
    · exact mem_range.mpr (mem_filter.mp hp).2
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hQ
      obtain ⟨_,yl,yr⟩ := mem_filter.mp hy
      exact mem_range.mpr (by omega)
  have cq : Q.card=U.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    have hxn := (mem_filter.mp hx).2.2
    have hyn := (mem_filter.mp hy).2.2
    change n-1-x=n-1-y at e
    omega
  have he : B.filter (· < n) = B.filter (· < n-q) ∪ U := by
    ext x
    simp only [U,mem_filter,mem_union]
    by_cases hx : x ∈ B
    · simp only [hx,true_and]
      omega
    · simp only [hx,false_and,false_or]
  have hd : Disjoint (B.filter (· < n-q)) U := by
    apply disjoint_left.mpr
    intro y ha hb
    exact (not_lt_of_ge (mem_filter.mp hb).2.1) (mem_filter.mp ha).2
  have hh := card_le_card sub
  rw [card_union_of_disjoint dis,card_range,cq] at hh
  change count A q + U.card ≤ q at hh
  have ef : count B n = count B (n-q)+U.card := by rw [count,he,card_union_of_disjoint hd]; rfl
  omega

/-- Two balanced prefixes, with the first ending at a height that bounds
all heights of the second, cover the entire second prefix after addition
of the two possible cell-endpoint offsets. -/
theorem prefix_sum_coverage (A B : Finset ℕ) {m N h : ℕ}
    (hA : ∀ i ≤ m, i ≤ 2*count A i) (peak : 2*count A m = m+h)
    (hB : ∀ i ≤ N, i ≤ 2*count B i ∧ 2*count B i ≤ i+h)
    (k : ℕ) (hk : k < N) : k ∈ (A+B)+range 2 := by
  by_contra missing
  have noAdd (x : ℕ) (hx : x ∈ half A) (y : ℕ) (hy : y ∈ half B) : x+y+1 ≠ 2*k+1 := by
    intro he
    obtain ⟨i,hi,e1⟩ := mem_half.mp hx
    obtain ⟨j,hj,e2⟩ := mem_half.mp hy
    have either : k=i+j ∨ k=i+j+1 := by omega
    have hsum := mem_add.mpr ⟨i,hi,j,hj,rfl⟩
    apply missing
    rcases either with eq | eq
    · exact mem_add.mpr ⟨i+j,hsum,0,by decide,by omega⟩
    · exact mem_add.mpr ⟨i+j,hsum,1,by decide,by omega⟩
  obtain ⟨b0,_⟩ := hB k (by omega)
  obtain ⟨b1,_⟩ := hB (k+1) (by omega)
  by_cases km : k < m
  · have hc := reflect_before (half A) (half B) (q:=2*k+1) (le_refl _) noAdd
    rw [Nat.sub_self,show count (half B) 0=0 by simp [count],add_zero,
      half_count A k 1 (by decide),half_count B k 1 (by decide)] at hc
    have a0 := hA k (by omega)
    have a1 := hA (k+1) (by omega)
    omega
  · let r := k-m
    have er : r+m=k := Nat.sub_add_cancel (by omega)
    obtain ⟨_,br0⟩ := hB r (by omega)
    obtain ⟨_,br1⟩ := hB (r+1) (by omega)
    have hc := reflect_before (half A) (half B) (q:=2*m) (by omega) noAdd
    have ea := half_count A m 0 (by decide)
    simp only [add_zero] at ea
    rw [ea,half_count B k 1 (by decide),show 2*k+1-2*m=2*r+1 by omega,
      half_count B r 1 (by decide)] at hc
    omega



open Finset
open scoped Pointwise

theorem count_zero (A : Finset ℕ) : count A 0 = 0 := by simp [count]

theorem count_succ (A : Finset ℕ) (j : ℕ) :
    count A (j+1) = count A j + if j ∈ A then 1 else 0 := by
  classical
  by_cases hit : j ∈ A
  · have eq : A.filter (· < j+1) = insert j (A.filter (· < j)) := by
      ext z
      simp only [mem_filter,mem_insert]
      constructor
      · rintro ⟨hz,hl⟩
        by_cases ze : z=j
        · exact Or.inl ze
        · exact Or.inr ⟨hz,by omega⟩
      · rintro (rfl|⟨hz,hl⟩)
        · exact ⟨hit,by omega⟩
        · exact ⟨hz,by omega⟩
    unfold count
    rw [eq,card_insert_of_notMem (by simp),if_pos hit]
  · have eq : A.filter (· < j+1) = A.filter (· < j) := by
      ext z
      simp only [mem_filter]
      constructor
      · rintro ⟨hz,hl⟩
        have zn : z ≠ j := fun e => hit (e ▸ hz)
        exact ⟨hz,by omega⟩
      · rintro ⟨hz,hl⟩
        exact ⟨hz,by omega⟩
    unfold count
    rw [eq,if_neg hit,Nat.add_zero]

/-- The initial balanced excursion in the path with rises on members and
falls on missing integers. The given height occurs at a prefix of length k. -/
structure Excursion (A : Finset ℕ) (m h : ℕ) : Prop where
  ends : 2*count A m = m
  gap : m ∉ A
  bounds : ∀ i ≤ m, i ≤ 2*count A i ∧ 2*count A i ≤ i+h
  peak : ∃ k ≤ m, 2*count A k = k+h

theorem exists_excursion (A : Finset ℕ) : ∃ m h, Excursion A m h := by
  classical
  have stop : ∃ j, 2*count A j < j := by
    refine ⟨2*A.card+1,?_⟩
    have c : count A (2*A.card+1) ≤ A.card := card_filter_le _ _
    omega
  let s := Nat.find stop
  have fail : 2*count A s < s := Nat.find_spec stop
  have init (i : ℕ) (hi : i < s) : i ≤ 2*count A i :=
    Nat.le_of_not_gt (Nat.find_min stop hi)
  have spos : 0 < s := by omega
  let m := s-1
  have ms : m+1=s := by dsimp [m]; omega
  have base := init m (by omega)
  have step := count_succ A m
  rw [ms] at step
  have gap : m ∉ A := by
    intro hit
    rw [if_pos hit] at step
    omega
  rw [if_neg gap] at step
  have ends : 2*count A m = m := by omega
  let levels := (range (m+1)).image (fun i => 2*count A i-i)
  have nz : levels.Nonempty := ⟨_,mem_image.mpr ⟨0,mem_range.mpr (by omega),rfl⟩⟩
  let h := levels.max' nz
  obtain ⟨k,hk,eq⟩ := mem_image.mp (max'_mem levels nz)
  have kl : k < m+1 := mem_range.mp hk
  have kb := init k (by omega)
  have top : 2*count A k-k=h := eq
  refine ⟨m,h,ends,gap,?_,k,by omega,by omega⟩
  intro i hi
  have ib := init i (by omega)
  have le : 2*count A i-i ≤ h := le_max' levels _ (mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩)
  exact ⟨ib,by omega⟩

theorem excursion_nonempty {A : Finset ℕ} {m h : ℕ} (head : Excursion A m h)
    (begins : 0 ∈ A) : 0 < m ∧ 0 < h ∧ 0 < count A m := by
  have hm : 0 < m := by
    by_contra! hz
    exact head.gap (by simpa [show m=0 by omega] using begins)
  have one := count_succ A 0
  rw [count_zero,if_pos begins] at one
  have bound := (head.bounds 1 (by omega)).2
  have endBound := head.ends
  change count A 1 = 1 at one
  exact ⟨hm,by omega,by omega⟩

theorem excursion_sum_coverage (A B : Finset ℕ) {m n d e : ℕ}
    (left : Excursion A m d) (right : Excursion B n e) (le : e ≤ d) (k : ℕ) (hk : k<n) :
    k ∈ (A+B)+range 2 := by
  obtain ⟨x,hx,peak⟩ := left.peak
  refine prefix_sum_coverage A B (m:=x) (N:=n) (h:=d) (fun i hi => (left.bounds i (hi.trans hx)).1)
    peak (fun i hi => ?_) k hk
  obtain ⟨pos,neg⟩ := right.bounds i hi
  exact ⟨pos,by omega⟩



open Finset
open scoped Pointwise

def tail (A : Finset ℕ) (p : ℕ) := (A.filter (p ≤ ·)).image (·-p)

theorem mem_tail {A : Finset ℕ} {p x : ℕ} : x ∈ tail A p ↔ p+x ∈ A := by
  constructor
  · intro hit
    obtain ⟨y,hy,e⟩ := mem_image.mp hit
    obtain ⟨hy,lo⟩ := mem_filter.mp hy
    have eq : p+x=y := by change y-p=x at e; omega
    rwa [eq]
  · intro hit
    exact mem_image.mpr ⟨p+x,mem_filter.mpr ⟨hit,by omega⟩,by omega⟩

theorem tail_count (A : Finset ℕ) (p n : ℕ) :
    count (tail A p) n = (A.filter (fun x => p ≤ x ∧ x < p+n)).card := by
  let U := A.filter (fun x => p ≤ x ∧ x < p+n)
  have eq : (tail A p).filter (· < n) = U.image (·-p) := by
    ext x
    constructor
    · intro h
      obtain ⟨hx,lt⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨p+x,mem_filter.mpr ⟨mem_tail.mp hx,by omega,by omega⟩,by omega⟩
    · intro h
      obtain ⟨y,hy,e⟩ := mem_image.mp h
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hy
      change y-p=x at e
      exact mem_filter.mpr ⟨mem_tail.mpr (by rwa [show p+x=y by omega]),by omega⟩
  unfold count
  rw [eq]
  apply card_image_of_injOn
  intro x hx y hy he
  have xl := (mem_filter.mp hx).2.1
  have yl := (mem_filter.mp hy).2.1
  change x-p=y-p at he
  omega

/-- Every interval has discrepancy at most D. -/
def Capped (A : Finset ℕ) (D : ℕ) : Prop := ∀ p n, 2*count (tail A p) n ≤ n+D

theorem capped_mono {A B : Finset ℕ} {D : ℕ} (sub : A ⊆ B) (h : Capped B D) :
    Capped A D := by
  intro p n
  have z := h p n
  rw [tail_count] at z ⊢
  have k := card_le_card (filter_subset_filter (fun x : ℕ => p ≤ x ∧ x < p+n) sub)
  omega

theorem lift_sum {A B : Finset ℕ} {b k : ℕ} (h : k ∈ (A+tail B b)+range 2) :
    b+k ∈ (A+B)+range 2 := by
  obtain ⟨t,ht,e,he,eq⟩ := mem_add.mp h
  obtain ⟨i,hi,j,hj,et⟩ := mem_add.mp ht
  exact mem_add.mpr ⟨i+(b+j),mem_add.mpr ⟨i,hi,b+j,mem_tail.mp hj,rfl⟩,e,he,by omega⟩

theorem anchored_sum (A : Finset ℕ) {m D : ℕ}
    (balance : ∀ i ≤ m, i ≤ 2*count A i) (peak : 2*count A m=m+D)
    (B : Finset ℕ) (M : ℕ) (capped : Capped B D) (bounded : ∀ x ∈ B, x < M) :
    2*B.card ≤ (((A+B)+range 2).filter (· < M+D)).card := by
  classical
  induction hN : B.card using Nat.strong_induction_on generalizing B with
  | h N ih =>
    by_cases empty : B = ∅
    · have z : N=0 := by simpa [empty] using hN.symm
      simp [z]
    have ne := nonempty_iff_ne_empty.mpr empty
    let b := B.min' ne
    have hb : b ∈ B := min'_mem B ne
    have low (x : ℕ) (hx : x ∈ B) : b ≤ x := min'_le B x hx
    obtain ⟨n,e,head⟩ := exists_excursion (tail B b)
    have starts : 0 ∈ tail B b := mem_tail.mpr (by simpa using hb)
    obtain ⟨hn,_,hcount⟩ := excursion_nonempty head starts
    obtain ⟨k,_,hp⟩ := head.peak
    have cap := capped b k
    have hD : e ≤ D := by omega
    let U := B.filter (· < b+n)
    let V := B.filter (b+n ≤ ·)
    have cu : count (tail B b) n = U.card := by
      rw [tail_count]
      congr 1
      ext x
      simp only [U,mem_filter]
      exact ⟨fun ⟨hit,_,hi⟩ => ⟨hit,hi⟩,fun ⟨hit,hi⟩ => ⟨hit,low x hit,hi⟩⟩
    have partition : U.card+V.card=B.card := by
      have part := card_filter_add_card_filter_not (s:=B) (fun x => x < b+n)
      simpa only [U,V,not_lt] using part
    have less : V.card < N := by omega
    have sub : V ⊆ B := filter_subset _ _
    have other := ih V.card less V (capped_mono sub capped) (fun x hx => bounded x (sub hx)) rfl
    have bound_n : b+n ≤ M+D := by
      by_contra! large
      have src := capped b (M-b)
      have full : count (tail B b) (M-b)=count (tail B b) n := by
        unfold count
        congr 1
        ext x
        simp only [mem_filter,mem_tail]
        constructor
        · rintro ⟨hit,hi⟩
          exact ⟨hit,by omega⟩
        · rintro ⟨hit,hi⟩
          have h := bounded (b+x) hit
          exact ⟨hit,by omega⟩
      rw [full,head.ends] at src
      have bm := bounded b hb
      omega
    let S := ((A+V)+range 2).filter (· < M+D)
    let K := Ico b (b+n)
    have sep : Disjoint K S := by
      apply disjoint_left.mpr
      intro x hk hs
      have hi := (mem_Ico.mp hk).2
      obtain ⟨t,ht,z,_,he⟩ := mem_add.mp (mem_filter.mp hs).1
      obtain ⟨i,_,j,hj,eq⟩ := mem_add.mp ht
      have lo := (mem_filter.mp hj).2
      omega
    have all : K ∪ S ⊆ ((A+B)+range 2).filter (· < M+D) := by
      intro x hx
      rcases mem_union.mp hx with hk|hs
      · obtain ⟨lo,up⟩ := mem_Ico.mp hk
        have cov := prefix_sum_coverage A (tail B b) (N:=n) balance peak
          (fun i hi => ⟨(head.bounds i hi).1,(head.bounds i hi).2.trans (by omega)⟩)
          (x-b) (by omega)
        have lifted := lift_sum cov
        have eq : b+(x-b)=x := by omega
        exact mem_filter.mpr ⟨eq ▸ lifted,by omega⟩
      · obtain ⟨hit,lt⟩ := mem_filter.mp hs
        obtain ⟨t,ht,e,he,eq⟩ := mem_add.mp hit
        obtain ⟨i,hi,j,hj,et⟩ := mem_add.mp ht
        exact mem_filter.mpr ⟨mem_add.mpr ⟨t,mem_add.mpr ⟨i,hi,j,sub hj,et⟩,e,he,eq⟩,lt⟩
    have final := card_le_card all
    rw [card_union_of_disjoint sep] at final
    have ck : K.card=n := by simp [K]
    have endcard := head.ends
    change 2*V.card ≤ S.card at other
    omega



open Finset
open scoped Pointwise

theorem tail_zero (A : Finset ℕ) : tail A 0=A := by ext x; simp [mem_tail]
theorem tail_tail (A : Finset ℕ) (p j : ℕ) : tail (tail A p) j=tail A (p+j) := by
  ext x
  simp only [mem_tail,Nat.add_assoc]

theorem count_split (A : Finset ℕ) (p n : ℕ) :
    count A (p+n)=count A p+count (tail A p) n := by
  rw [tail_count]
  have split : A.filter (· < p+n) =
      A.filter (· < p) ∪ A.filter (fun x => p ≤ x ∧ x < p+n) := by
    ext x
    simp only [mem_filter,mem_union]
    constructor
    · rintro ⟨hit,hi⟩
      by_cases lo : x < p
      · exact Or.inl ⟨hit,lo⟩
      · exact Or.inr ⟨hit,by omega,hi⟩
    · rintro (⟨hit,lo⟩|⟨hit,lo,hi⟩) <;> exact ⟨hit,by omega⟩
  have dis : Disjoint (A.filter (· < p)) (A.filter (fun x => p ≤ x ∧ x < p+n)) := by
    apply disjoint_left.mpr
    intro x hl hr
    exact (not_lt_of_ge (mem_filter.mp hr).2.1) (mem_filter.mp hl).2
  unfold count
  rw [split,card_union_of_disjoint dis]

theorem cap_tail {A : Finset ℕ} {D : ℕ} (h : Capped A D) (j : ℕ) :
    Capped (tail A j) D := by
  intro p n
  rw [tail_tail]
  exact h _ _

def Reaches (A : Finset ℕ) (D : ℕ) : Prop :=
  ∃ p n, n+D ≤ 2*count (tail A p) n

theorem reaches_tail_after_excursion {A : Finset ℕ} {D m h : ℕ}
    (big : Reaches A D) (head : Excursion A m h) (small : h<D) : Reaches (tail A m) D := by
  obtain ⟨p,n,rise⟩ := big
  by_cases pm : m ≤ p
  · refine ⟨p-m,n,?_⟩
    rwa [tail_tail,show m+(p-m)=p by omega]
  have diff := count_split A p n
  have ppos := (head.bounds p (by omega)).1
  have behind : m ≤ p+n := by
    by_contra! early
    have cap := (head.bounds (p+n) early.le).2
    omega
  refine ⟨0,p+n-m,?_⟩
  rw [tail_zero]
  have diff' := count_split A m (p+n-m)
  rw [show m+(p+n-m)=p+n by omega] at diff'
  have endval := head.ends
  omega

theorem reaches_normalize {A : Finset ℕ} {D b : ℕ}
    (positive : 0<D) (big : Reaches A D) (lower : ∀ x ∈ A, b ≤ x) : Reaches (tail A b) D := by
  obtain ⟨p,n,rise⟩ := big
  by_cases pb : b ≤ p
  · refine ⟨p-b,n,?_⟩
    rwa [tail_tail,show b+(p-b)=p by omega]
  have zero (j : ℕ) (hj : j ≤ b) : count A j=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h1 := (mem_filter.mp hx).2
    have h2 := lower x (mem_filter.mp hx).1
    omega
  have d := count_split A p n
  have zp := zero p (by omega)
  have endpos : b ≤ p+n := by
    by_contra! prior
    have z := zero (p+n) prior.le
    omega
  refine ⟨0,p+n-b,?_⟩
  rw [tail_zero]
  have d' := count_split A b (p+n-b)
  rw [show b+(p+n-b)=p+n by omega] at d'
  have zb := zero b le_rfl
  omega

theorem tail_card (A : Finset ℕ) (b : ℕ) : (tail A b).card=(A.filter (b ≤ ·)).card := by
  apply card_image_of_injOn
  intro x hx y hy e
  have xl := (mem_filter.mp hx).2
  have yl := (mem_filter.mp hy).2
  change x-b=y-b at e
  omega

theorem normalize_card {A : Finset ℕ} {b : ℕ} (lower : ∀ x ∈ A,b ≤ x) : (tail A b).card=A.card := by
  rw [tail_card,filter_eq_self.mpr lower]

def reverse (A : Finset ℕ) (M : ℕ) := A.image (M-·)

theorem mem_reverse {A : Finset ℕ} {M x : ℕ} (bound : ∀ y ∈ A, y ≤ M) :
    x ∈ reverse A M ↔ x ≤ M ∧ M-x ∈ A := by
  constructor
  · intro hit
    obtain ⟨y,hy,e⟩ := mem_image.mp hit
    change M-y=x at e
    have lim := bound y hy
    exact ⟨by omega,by rwa [show M-x=y by omega]⟩
  · rintro ⟨lo,hit⟩
    exact mem_image.mpr ⟨M-x,hit,by omega⟩

theorem reverse_card {A : Finset ℕ} {M : ℕ} (bound : ∀ y ∈ A,y ≤ M) :
    (reverse A M).card=A.card := by
  apply card_image_of_injOn
  intro x hx y hy e
  have xl := bound x hx; have yl := bound y hy
  change M-x=M-y at e
  omega

theorem reverse_inv {A : Finset ℕ} {M : ℕ} (bound : ∀ y ∈ A,y ≤ M) :
    reverse (reverse A M) M=A := by
  have rhs (y : ℕ) (hy : y ∈ reverse A M) := (mem_reverse bound |>.mp hy).1
  ext x
  rw [mem_reverse rhs,mem_reverse bound]
  constructor
  · rintro ⟨lo,_,hit⟩
    rwa [show M-(M-x)=x by omega] at hit
  · intro hit
    have xl := bound x hit
    exact ⟨xl,by omega,by rwa [show M-(M-x)=x by omega]⟩

theorem reverse_prefix {A : Finset ℕ} {M : ℕ} (bound : ∀ y ∈ A,y ≤ M)
    {p n : ℕ} (inside : p+n ≤ M+1) :
    count (tail (reverse A M) p) n = count (tail A (M+1-(p+n))) n := by
  rw [tail_count,tail_count]
  let U := A.filter (fun x => M+1-(p+n) ≤ x ∧ x < M+1-(p+n)+n)
  have e : (reverse A M).filter (fun x => p ≤ x ∧ x < p+n) = reverse U M := by
    ext x
    rw [mem_filter,mem_reverse bound,mem_reverse (fun y hy => bound y (mem_filter.mp hy).1)]
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨lo,hit⟩,left,right⟩
      exact ⟨lo,hit,by omega,by omega⟩
    · rintro ⟨lo,hit,left,right⟩
      exact ⟨⟨lo,hit⟩,by omega,by omega⟩
  rw [e,reverse_card (fun y hy => bound y (mem_filter.mp hy).1)]

theorem count_clip {A : Finset ℕ} {M : ℕ} (bound : ∀ y ∈ A,y ≤ M) (p n : ℕ) :
    count (tail A p) n = count (tail A p) (min n (M+1-p)) := by
  rw [tail_count,tail_count]
  congr 1
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hit,lo,hi⟩
    have max := bound x hit
    exact ⟨hit,lo,by omega⟩
  · rintro ⟨hit,lo,hi⟩
    exact ⟨hit,lo,by omega⟩

theorem cap_reverse {A : Finset ℕ} {M D : ℕ} (bound : ∀ y ∈ A,y ≤ M) (cap : Capped A D) :
    Capped (reverse A M) D := by
  have bound' (y : ℕ) (hy : y ∈ reverse A M) := (mem_reverse bound |>.mp hy).1
  intro p n
  rw [count_clip bound' p n]
  by_cases high : M+1<p
  · simp [show M+1-p=0 by omega,count_zero]
  rw [reverse_prefix bound (by omega)]
  have c := cap (M+1-(p+min n (M+1-p))) (min n (M+1-p))
  omega

theorem reaches_reverse {A : Finset ℕ} {M D : ℕ} (bound : ∀ y ∈ A,y ≤ M)
    (pos : 0<D) (big : Reaches A D) : Reaches (reverse A M) D := by
  obtain ⟨p,n,rise⟩ := big
  let w := min n (M+1-p)
  have orig := count_clip bound p n
  change count (tail A p) n = count (tail A p) w at orig
  have wpos : 0<w := by
    by_contra! hp
    have wz : w=0 := by omega
    rw [wz,count_zero] at orig
    omega
  have wl : p+w ≤ M+1 := by dsimp [w] at *; omega
  have wn : w ≤ n := min_le_left _ _
  refine ⟨M+1-(p+w),w,?_⟩
  rw [reverse_prefix bound (by omega),show M+1-(M+1-(p+w)+w)=p by omega]
  omega



open Finset
open scoped Pointwise

def sums (A B : Finset ℕ) := (A+B)+range 2

theorem mem_sums {A B : Finset ℕ} {t : ℕ} :
    t ∈ sums A B ↔ ∃ x ∈ A, ∃ y ∈ B, ∃ e ≤ 1,x+y+e=t := by
  constructor
  · intro hit
    obtain ⟨s,hs,e,he,rfl⟩ := mem_add.mp hit
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hs
    exact ⟨x,hx,y,hy,e,by have z := mem_range.mp he; omega,rfl⟩
  · rintro ⟨x,hx,y,hy,e,he,rfl⟩
    exact mem_add.mpr ⟨x+y,mem_add.mpr ⟨x,hx,y,hy,rfl⟩,e,mem_range.mpr (by omega),rfl⟩

theorem sums_comm (A B : Finset ℕ) : sums A B=sums B A := by unfold sums; rw [add_comm A B]

theorem normalize_sums {A B : Finset ℕ} {a b : ℕ} (loA : ∀x ∈ A,a ≤ x)
    (loB : ∀x ∈ B,b ≤ x) : (sums (tail A a) (tail B b)).card = (sums A B).card := by
  let U := sums (tail A a) (tail B b)
  have eq : U.image (fun x => a+b+x)=sums A B := by
    ext t
    constructor
    · intro h
      obtain ⟨z,hz,e⟩ := mem_image.mp h
      obtain ⟨x,hx,y,hy,k,hk,et⟩ := mem_sums.mp hz
      exact mem_sums.mpr ⟨a+x,mem_tail.mp hx,b+y,mem_tail.mp hy,k,hk,by omega⟩
    · intro h
      obtain ⟨x,hx,y,hy,k,hk,e⟩ := mem_sums.mp h
      have xl := loA x hx
      have yl := loB y hy
      exact mem_image.mpr ⟨x-a+(y-b)+k,mem_sums.mpr
        ⟨x-a,mem_tail.mpr (by rwa [show a+(x-a)=x by omega]),
         y-b,mem_tail.mpr (by rwa [show b+(y-b)=y by omega]),k,hk,rfl⟩,by omega⟩
  have card := card_image_of_injective U (add_right_injective (a+b))
  rwa [eq,eq_comm] at card

theorem sums_bound {A B : Finset ℕ} {M N : ℕ} (ha : ∀x ∈ A,x ≤ M) (hb : ∀y ∈ B,y ≤ N)
    {x : ℕ} (hx : x ∈ sums A B) : x ≤ M+N+1 := by
  obtain ⟨i,hi,j,hj,k,hk,e⟩ := mem_sums.mp hx
  have ai := ha i hi; have bj := hb j hj
  omega

theorem reverse_sums {A B : Finset ℕ} {M N : ℕ}
    (ha : ∀x ∈ A,x ≤ M) (hb : ∀y ∈ B,y ≤ N) :
    sums (reverse A M) (reverse B N)=reverse (sums A B) (M+N+1) := by
  ext t
  rw [mem_reverse (fun _ hx => sums_bound ha hb hx)]
  constructor
  · intro hit
    obtain ⟨i,hi,j,hj,e,he,eq⟩ := mem_sums.mp hit
    obtain ⟨il,ai⟩ := (mem_reverse ha).mp hi
    obtain ⟨jl,bj⟩ := (mem_reverse hb).mp hj
    exact ⟨by omega,mem_sums.mpr ⟨M-i,ai,N-j,bj,1-e,by omega,by omega⟩⟩
  · rintro ⟨tl,hit⟩
    obtain ⟨i,hi,j,hj,e,he,eq⟩ := mem_sums.mp hit
    have il := ha i hi
    have jl := hb j hj
    exact mem_sums.mpr ⟨M-i,mem_image.mpr ⟨i,hi,rfl⟩,N-j,mem_image.mpr ⟨j,hj,rfl⟩,
      1-e,by omega,by omega⟩

def Bound (A B : Finset ℕ) (D : ℕ) : Prop := 2*A.card+2*B.card ≤ (sums A B).card+2*D

theorem opposite_anchors {A B : Finset ℕ} {M N D m n : ℕ}
    (ha : ∀x ∈ A,x ≤ M) (hb : ∀y ∈ B,y ≤ N) (ca : Capped A D) (cb : Capped B D)
    (front : Excursion A m D) (back : Excursion (reverse B N) n D) : Bound A B D := by
  obtain ⟨k,km,pk⟩ := front.peak
  obtain ⟨j,jn,pj⟩ := back.peak
  let S := sums A B
  let P := S.filter (· < N+1+D)
  let Q := S.filter (fun x => N+1 ≤ x+D)
  have left : 2*B.card ≤ P.card := anchored_sum A (fun i hi => (front.bounds i (hi.trans km)).1)
    pk B (N+1) cb (fun x hx => Nat.lt_succ_of_le (hb x hx))
  have right := anchored_sum (reverse B N) (fun i hi => (back.bounds i (hi.trans jn)).1)
    pj (reverse A M) (M+1) (cap_reverse ha ca)
    (fun x hx => Nat.lt_succ_of_le ((mem_reverse ha).mp hx).1)
  change 2*(reverse A M).card ≤ ((sums (reverse B N) (reverse A M)).filter (· < M+1+D)).card at right
  rw [reverse_card ha,sums_comm,reverse_sums ha hb] at right
  have eq : (reverse (sums A B) (M+N+1)).filter (· < M+1+D) = reverse Q (M+N+1) := by
    ext x
    rw [mem_filter,mem_reverse (fun _ hx => sums_bound ha hb hx),
      mem_reverse (fun _ hx => sums_bound ha hb (mem_filter.mp hx).1)]
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨xl,hit⟩,hi⟩
      exact ⟨xl,hit,by omega⟩
    · rintro ⟨xl,hit,hi⟩
      exact ⟨⟨xl,hit⟩,by omega⟩
  rw [eq,reverse_card (fun _ hx => sums_bound ha hb (mem_filter.mp hx).1)] at right
  have overlap : P ∩ Q ⊆ Ico (N+1-D) (N+1+D) := by
    intro x hx
    obtain ⟨hp,hq⟩ := mem_inter.mp hx
    have hi := (mem_filter.mp hp).2; have lo := (mem_filter.mp hq).2
    exact mem_Ico.mpr ⟨by omega,hi⟩
  have cap := card_le_card overlap
  rw [Nat.card_Ico] at cap
  have join : P ∪ Q ⊆ S := union_subset (filter_subset _ _) (filter_subset _ _)
  change 2*A.card ≤ Q.card at right
  have upper := card_le_card join
  have sum := card_union_add_card_inter P Q
  change 2*A.card+2*B.card ≤ S.card+2*D
  omega

def Smaller (N D : ℕ) := ∀ A B : Finset ℕ, A.card+B.card < N → Capped A D → Capped B D →
  Reaches A D → Reaches B D → Bound A B D

theorem bound_comm (A B : Finset ℕ) (D : ℕ) : Bound A B D ↔ Bound B A D := by
  unfold Bound
  rw [sums_comm,add_comm (2*A.card) (2*B.card)]

theorem peel {A B : Finset ℕ} {m n e d D : ℕ}
    (_za : 0 ∈ A) (zb : 0 ∈ B) (a : Excursion A m e) (b : Excursion B n d) (fits : d ≤ e)
    (small : d<D) (ca : Capped A D) (cb : Capped B D) (pa : Reaches A D) (pb : Reaches B D)
    (ih : Smaller (A.card+B.card) D) : Bound A B D := by
  let V := B.filter (n ≤ ·)
  have pv : Reaches V D := by
    obtain ⟨p,w,h⟩ := reaches_tail_after_excursion pb b small
    rw [tail_tail] at h
    have eq : tail V (n+p)=tail B (n+p) := by
      ext x
      simp only [V,mem_tail,mem_filter]
      exact ⟨And.left,fun hit => ⟨hit,by omega⟩⟩
    exact ⟨n+p,w,by rwa [eq]⟩
  have part : count B n+V.card=B.card := by
    simpa only [count,V,not_lt] using card_filter_add_card_filter_not (s:=B) (fun x => x<n)
  have hn := (excursion_nonempty b zb).2.2
  have sub : V ⊆ B := filter_subset _ _
  have smallerResult := ih A V (by omega) ca (capped_mono sub cb) pa pv
  have sep : Disjoint (range n) (sums A V) := by
    apply disjoint_left.mpr
    intro x hx hit
    obtain ⟨i,_,j,hj,k,_,eq⟩ := mem_sums.mp hit
    have lo := (mem_filter.mp hj).2; have hi := mem_range.mp hx
    omega
  have all : range n ∪ sums A V ⊆ sums A B := by
    intro x hx
    rcases mem_union.mp hx with hr|hs
    · exact excursion_sum_coverage A B a b fits x (mem_range.mp hr)
    · obtain ⟨i,hi,j,hj,k,hk,eq⟩ := mem_sums.mp hs
      exact mem_sums.mpr ⟨i,hi,j,sub hj,k,hk,eq⟩
  have lower := card_le_card all
  rw [card_union_of_disjoint sep,card_range] at lower
  have ends := b.ends
  unfold Bound at smallerResult ⊢
  omega

theorem front_alternative {A B : Finset ℕ} {D : ℕ}
    (za : 0 ∈ A) (zb : 0 ∈ B) (ca : Capped A D) (cb : Capped B D)
    (pa : Reaches A D) (pb : Reaches B D) (ih : Smaller (A.card+B.card) D) :
    Bound A B D ∨ (∃ m, Excursion A m D) ∧ ∃ n, Excursion B n D := by
  obtain ⟨m,e,a⟩ := exists_excursion A
  obtain ⟨n,d,b⟩ := exists_excursion B
  obtain ⟨i,_,ha⟩ := a.peak
  obtain ⟨j,_,hb⟩ := b.peak
  have ea := ca 0 i; have eb := cb 0 j
  rw [tail_zero] at ea eb
  by_cases ds : d<D ∧ d≤e
  · exact Or.inl (peel za zb a b ds.2 ds.1 ca cb pa pb ih)
  by_cases es : e<D ∧ e≤d
  · have ih' : Smaller (B.card+A.card) D := by rwa [Nat.add_comm B.card A.card]
    exact Or.inl ((bound_comm A B D).mpr (peel zb za b a es.2 es.1 cb ca pb pa ih'))
  have eD : e=D := by omega
  have dD : d=D := by omega
  exact Or.inr ⟨⟨m,eD ▸ a⟩,n,dD ▸ b⟩

theorem normalized_double {A B : Finset ℕ} {D : ℕ}
    (pos : 0<D) (za : 0 ∈ A) (zb : 0 ∈ B) (ca : Capped A D) (cb : Capped B D)
    (pa : Reaches A D) (pb : Reaches B D) (ih : Smaller (A.card+B.card) D) : Bound A B D := by
  rcases front_alternative za zb ca cb pa pb ih with done|⟨⟨m,pa'⟩,_⟩
  · exact done
  let M := A.max' ⟨0,za⟩
  let N := B.max' ⟨0,zb⟩
  have ha (x : ℕ) (hx : x ∈ A) : x ≤ M := le_max' A x hx
  have hb (x : ℕ) (hx : x ∈ B) : x ≤ N := le_max' B x hx
  have ra : 0 ∈ reverse A M := (mem_reverse ha).mpr ⟨Nat.zero_le _,by simpa using max'_mem A ⟨0,za⟩⟩
  have rb : 0 ∈ reverse B N := (mem_reverse hb).mpr ⟨Nat.zero_le _,by simpa using max'_mem B ⟨0,zb⟩⟩
  have ih' : Smaller ((reverse A M).card+(reverse B N).card) D := by rwa [reverse_card ha,reverse_card hb]
  rcases front_alternative ra rb (cap_reverse ha ca) (cap_reverse hb cb)
    (reaches_reverse ha pos pa) (reaches_reverse hb pos pb) ih' with done|⟨_,⟨n,pb'⟩⟩
  · unfold Bound at done ⊢
    rwa [reverse_card ha,reverse_card hb,reverse_sums ha hb,reverse_card (fun _ hx => sums_bound ha hb hx)] at done
  · exact opposite_anchors ha hb ca cb pa' pb'

/-- Equal maximal discrepancies give a doubling estimate for the cell sumset. -/
theorem discrete_sumset {A B : Finset ℕ} {D : ℕ} (pos : 0<D)
    (ca : Capped A D) (cb : Capped B D) (pa : Reaches A D) (pb : Reaches B D) : Bound A B D := by
  classical
  induction hN : A.card+B.card using Nat.strong_induction_on generalizing A B with
  | h N ih =>
    have nonempty (S : Finset ℕ) (p : Reaches S D) : S.Nonempty := by
      by_contra! empty
      obtain ⟨j,w,h⟩ := p
      rw [empty] at h
      simp [tail,count] at h
      omega
    let a := A.min' (nonempty A pa)
    let b := B.min' (nonempty B pb)
    have a0 : 0 ∈ tail A a := mem_tail.mpr (by simpa using min'_mem A (nonempty A pa))
    have b0 : 0 ∈ tail B b := mem_tail.mpr (by simpa using min'_mem B (nonempty B pb))
    have loA (x : ℕ) (hx : x ∈ A) : a ≤ x := min'_le A x hx
    have loB (x : ℕ) (hx : x ∈ B) : b ≤ x := min'_le B x hx
    have ih' : Smaller ((tail A a).card+(tail B b).card) D := by
      rw [normalize_card loA,normalize_card loB,hN]
      intro T U sm ct cu pt pu
      exact ih _ sm ct cu pt pu rfl
    have res := normalized_double pos a0 b0 (cap_tail ca a) (cap_tail cb b)
      (reaches_normalize pos pa loA) (reaches_normalize pos pb loB) ih'
    unfold Bound at res ⊢
    rwa [normalize_card loA,normalize_card loB,normalize_sums loA loB] at res


end GreenFGY
open GreenFGY Finset

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1.H1 := by
  intro A B D pos ca cb pa pb
  have cap (S : Finset ℕ) (h : ∀ p n : ℕ,
      2*(S.filter (fun x => p ≤ x ∧ x<p+n)).card ≤ n+D) : Capped S D := by
    intro p n
    rw [tail_count]
    exact h p n
  have point (S : Finset ℕ) (h : ∃ p n : ℕ,
      n+D ≤ 2*(S.filter (fun x => p ≤ x ∧ x<p+n)).card) : Reaches S D := by
    obtain ⟨p,n,he⟩ := h
    exact ⟨p,n,by rwa [tail_count]⟩
  exact discrete_sumset pos (cap A ca) (cap B cb) (point A pa) (point B pb)

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H2

/- Original integer-cell proof by @Deldor14, based on the mathematical
arguments of Franchi, Gowers and Yip, arXiv:2607.06073. -/

namespace GreenFGY

open Finset
open scoped Pointwise
def count (T : Finset ℕ) (n : ℕ) := (T.filter (· < n)).card
def tail (A : Finset ℕ) (p : ℕ) := (A.filter (p ≤ ·)).image (·-p)

theorem mem_tail {A : Finset ℕ} {p x : ℕ} : x ∈ tail A p ↔ p+x ∈ A := by
  constructor
  · intro hit
    obtain ⟨y,hy,e⟩ := mem_image.mp hit
    obtain ⟨hy,lo⟩ := mem_filter.mp hy
    have eq : p+x=y := by change y-p=x at e; omega
    rwa [eq]
  · intro hit
    exact mem_image.mpr ⟨p+x,mem_filter.mpr ⟨hit,by omega⟩,by omega⟩

theorem tail_count (A : Finset ℕ) (p n : ℕ) :
    count (tail A p) n = (A.filter (fun x => p ≤ x ∧ x < p+n)).card := by
  let U := A.filter (fun x => p ≤ x ∧ x < p+n)
  have eq : (tail A p).filter (· < n) = U.image (·-p) := by
    ext x
    constructor
    · intro h
      obtain ⟨hx,lt⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨p+x,mem_filter.mpr ⟨mem_tail.mp hx,by omega,by omega⟩,by omega⟩
    · intro h
      obtain ⟨y,hy,e⟩ := mem_image.mp h
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hy
      change y-p=x at e
      exact mem_filter.mpr ⟨mem_tail.mpr (by rwa [show p+x=y by omega]),by omega⟩
  unfold count
  rw [eq]
  apply card_image_of_injOn
  intro x hx y hy he
  have xl := (mem_filter.mp hx).2.1
  have yl := (mem_filter.mp hy).2.1
  change x-p=y-p at he
  omega

theorem count_split (A : Finset ℕ) (p n : ℕ) :
    count A (p+n)=count A p+count (tail A p) n := by
  rw [tail_count]
  have split : A.filter (· < p+n) =
      A.filter (· < p) ∪ A.filter (fun x => p ≤ x ∧ x < p+n) := by
    ext x
    simp only [mem_filter,mem_union]
    constructor
    · rintro ⟨hit,hi⟩
      by_cases lo : x < p
      · exact Or.inl ⟨hit,lo⟩
      · exact Or.inr ⟨hit,by omega,hi⟩
    · rintro (⟨hit,lo⟩|⟨hit,lo,hi⟩) <;> exact ⟨hit,by omega⟩
  have dis : Disjoint (A.filter (· < p)) (A.filter (fun x => p ≤ x ∧ x < p+n)) := by
    apply disjoint_left.mpr
    intro x hl hr
    exact (not_lt_of_ge (mem_filter.mp hr).2.1) (mem_filter.mp hl).2
  unfold count
  rw [split,card_union_of_disjoint dis]


def sums (A B : Finset ℕ) := (A+B)+range 2
def reverse (A : Finset ℕ) (M : ℕ) := A.image (M-·)
theorem mem_sums {A B : Finset ℕ} {t : ℕ} :
    t ∈ sums A B ↔ ∃ x ∈ A, ∃ y ∈ B, ∃ e ≤ 1,x+y+e=t := by
  constructor
  · intro hit
    obtain ⟨s,hs,e,he,rfl⟩ := mem_add.mp hit
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hs
    exact ⟨x,hx,y,hy,e,by have z := mem_range.mp he; omega,rfl⟩
  · rintro ⟨x,hx,y,hy,e,he,rfl⟩
    exact mem_add.mpr ⟨x+y,mem_add.mpr ⟨x,hx,y,hy,rfl⟩,e,mem_range.mpr (by omega),rfl⟩

theorem difference_packing {T : Finset ℕ} {a u : ℕ} (apos : 0<a) (amin : ∀ x ∈ T,a ≤ x)
    (sep : ∀ i ∈ T,∀ j ∈ T,∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    let P := T.filter (· < u+a)
    (sums P (reverse P (u+a))).card+2*count T u ≤ 2*u := by
  classical
  let M := u+a
  let P := T.filter (· < M)
  let R := T.filter (· < u)
  let S := sums P (reverse P M)
  let X := R.image (fun x => M+x)
  let Y := R.image (fun x => M+1-x)
  have bnd (x : ℕ) (hx : x ∈ P) : x ≤ M := (mem_filter.mp hx).2.le
  have cx : X.card=R.card := card_image_of_injective _ (add_right_injective M)
  have cy : Y.card=R.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    have xl := (mem_filter.mp hx).2
    have yl := (mem_filter.mp hy).2
    change M+1-x=M+1-y at e
    dsimp [M] at *
    omega
  have xy : Disjoint X Y := by
    apply disjoint_left.mpr
    intro z hx hy
    obtain ⟨i,hi,e⟩ := mem_image.mp hx
    obtain ⟨j,hj,g⟩ := mem_image.mp hy
    have il := amin i (mem_filter.mp hi).1
    have jl := amin j (mem_filter.mp hj).1
    change M+i=z at e
    change M+1-j=z at g
    omega
  have pieces {z : ℕ} (h : z ∈ S) :
      ∃ i ∈ P, ∃ j ∈ P, ∃ e ≤ 1,z+j=M+i+e := by
    obtain ⟨i,hi,k,hk,e,he,eq⟩ := mem_sums.mp h
    obtain ⟨j,hj,hrev⟩ := mem_image.mp hk
    have jl := bnd j hj
    change M-j=k at hrev
    exact ⟨i,hi,j,hj,e,he,by omega⟩
  have free : Disjoint S (X ∪ Y) := by
    apply disjoint_left.mpr
    intro z hs bad
    obtain ⟨i,hi,j,hj,e,he,eq⟩ := pieces hs
    rcases mem_union.mp bad with x|y
    · obtain ⟨d,hd,ev⟩ := mem_image.mp x
      have v := sep j (mem_filter.mp hj).1 d (mem_filter.mp hd).1 i (mem_filter.mp hi).1
      change M+d=z at ev
      omega
    · obtain ⟨d,hd,ev⟩ := mem_image.mp y
      have v := sep i (mem_filter.mp hi).1 d (mem_filter.mp hd).1 j (mem_filter.mp hj).1
      have lim := (mem_filter.mp hd).2
      change M+1-d=z at ev
      dsimp [M] at *
      omega
  have sub : S ∪ (X ∪ Y) ⊆ Ico (a+1) (a+1+2*u) := by
    intro z hz
    rcases mem_union.mp hz with hs|rest
    · obtain ⟨i,hi,j,hj,e,he,eq⟩ := pieces hs
      have il := amin i (mem_filter.mp hi).1; have jl := amin j (mem_filter.mp hj).1
      have upper_i := (mem_filter.mp hi).2; have upper_j := (mem_filter.mp hj).2
      dsimp [M] at *
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    rcases mem_union.mp rest with h|h
    · obtain ⟨i,hi,eq⟩ := mem_image.mp h
      have il := amin i (mem_filter.mp hi).1
      have iu := (mem_filter.mp hi).2
      change M+i=z at eq
      dsimp [M] at eq
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨i,hi,eq⟩ := mem_image.mp h
      have il := amin i (mem_filter.mp hi).1
      have iu := (mem_filter.mp hi).2
      change M+1-i=z at eq
      dsimp [M] at eq
      exact mem_Ico.mpr ⟨by omega,by omega⟩
  have card := card_le_card sub
  rw [card_union_of_disjoint free,card_union_of_disjoint xy,cx,cy,Nat.card_Ico] at card
  change S.card+2*R.card ≤ 2*u
  omega

def block (T : Finset ℕ) (L w : ℕ) := T.filter (fun x => L ≤ x ∧ x<L+w)

theorem block_card_le (T : Finset ℕ) (L w : ℕ) : (block T L w).card ≤ w := by
  have sub : block T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
  simpa using card_le_card sub

theorem forced_gap {T : Finset ℕ} {a u L w D : ℕ} (wpos : 0<w) (short : w<a)
    (left : L ∈ T) (right : L+w-1 ∈ T)
    (sep : ∀ i ∈ T,∀ j ∈ T,∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (disc : w+D=2*(block T L w).card)
    (mass : count T u+2*count T (u+a) ≤ u+D)
    (failed : u+a ≤ count T u+count T (u+a)+count T (u+2*a)) :
    ∀ t ∈ T, t+L < u+a ∨ u+2*a < t+L+w := by
  intro t ht
  by_contra! cut
  obtain ⟨lo,hi⟩ := cut
  let C := block T L w
  let X := C.image (t+·)
  let R := block T (u+a) a
  let z := if u+a<t+L then t+L-1 else t+L+w
  have near : z+1=t+L ∨ z=t+(L+w-1)+1 := by
    dsimp [z]
    split <;> omega
  have zbound : z ∈ Ico (u+a) (u+2*a) := by
    dsimp [z]
    split <;> exact mem_Ico.mpr ⟨by omega,by omega⟩
  have znot : z ∉ T := by
    intro hit
    rcases near with e|e
    · have h := sep t ht L left z hit
      omega
    · have h := sep t ht (L+w-1) right z hit
      omega
  have zfree : z ∉ X := by
    intro hit
    obtain ⟨x,hx,e⟩ := mem_image.mp hit
    obtain ⟨_,xl,xr⟩ := mem_filter.mp hx
    change t+x=z at e
    omega
  have dis : Disjoint (insert z X) R := by
    apply disjoint_left.mpr
    intro x hx hr
    have hit := (mem_filter.mp hr).1
    rcases mem_insert.mp hx with e|inX
    · exact znot (e ▸ hit)
    obtain ⟨i,hi,eq⟩ := mem_image.mp inX
    have h := sep t ht i (mem_filter.mp hi).1 x hit
    change t+i=x at eq
    omega
  have sub : insert z X ∪ R ⊆ Ico (u+a) (u+2*a) := by
    intro x hx
    rcases mem_union.mp hx with inX|hr
    · rcases mem_insert.mp inX with rfl|inX
      · exact zbound
      obtain ⟨i,hi,eq⟩ := mem_image.mp inX
      obtain ⟨_,il,iu⟩ := mem_filter.mp hi
      change t+i=x at eq
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨_,l,r⟩ := mem_filter.mp hr
      exact mem_Ico.mpr ⟨l,by omega⟩
  have room := card_le_card sub
  have cx : X.card=C.card := card_image_of_injective C (add_right_injective t)
  rw [card_union_of_disjoint dis,card_insert_of_notMem zfree,cx,Nat.card_Ico] at room
  have split := count_split T (u+a) a
  rw [tail_count] at split
  change count T (u+a+a)=count T (u+a)+R.card at split
  rw [show u+a+a=u+2*a by omega] at split
  change count T (u+2*a)=count T (u+a)+R.card at split
  have cq := block_card_le T L w
  change w+D=2*C.card at disc
  change C.card ≤ w at cq
  omega


open Finset

theorem first_gap_width {T : Finset ℕ} {a u L w D : ℕ} (wpos : 0<w) (short : w<a)
    (left : L ∈ T) (right : L+w-1 ∈ T)
    (sep : ∀ i ∈ T,∀ j ∈ T,∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (disc : w+D=2*(block T L w).card) (mass : count T u+2*count T (u+a) ≤ u+D)
    (failed : u+a ≤ count T u+count T (u+a)+count T (u+2*a))
    {t v : ℕ} (ht : t ∈ T) (hv : v ∈ T) (before : t+L < u+a) (after : u+a ≤ v+L) :
    t+a ≤ v := by
  have cut := forced_gap wpos short left right sep disc mass failed v hv
  have reaches : u+2*a<v+L+w := by omega
  by_contra! narrow
  let R := block T (u+a) a
  let C := block T L w
  let H := Ico L (L+w) \ C
  let X := H.image (t+·)
  let Y := H.image (v+·)
  let J := Ico (t+L+w) (v+L)
  have ci : C ⊆ Ico L (L+w) := fun _ hi => mem_Ico.mpr (mem_filter.mp hi).2
  have ch : H.card=w-C.card := by rw [card_sdiff_of_subset ci]; simp
  have cx : X.card=H.card := card_image_of_injective _ (add_right_injective t)
  have cy : Y.card=H.card := card_image_of_injective _ (add_right_injective v)
  have hole {k x : ℕ} (hk : k ∈ T) (hit : x ∈ T) (lo : k+L ≤ x) (hi : x < k+L+w) :
      x ∈ H.image (k+·) := by
    apply mem_image.mpr
    refine ⟨x-k,mem_sdiff.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
    intro hc
    have bad := sep k hk (x-k) (mem_filter.mp hc).1 x hit
    omega
  have sub : R ⊆ (X ∪ Y) ∪ J := by
    intro x hx
    obtain ⟨hit,lo,hi⟩ := mem_filter.mp hx
    by_cases loc : x<t+L+w
    · exact mem_union_left _ (mem_union_left _ (hole ht hit (by omega) loc))
    by_cases loc' : v+L ≤ x
    · exact mem_union_left _ (mem_union_right _ (hole hv hit loc' (by omega)))
    · exact mem_union_right _ (mem_Ico.mpr ⟨by omega,by omega⟩)
  have upper := card_le_card sub
  have upper' := card_union_le (X ∪ Y) J
  have upper'' := card_union_le X Y
  have cj : J.card=(v+L)-(t+L+w) := Nat.card_Ico _ _
  have s := count_split T (u+a) a
  rw [tail_count] at s
  change count T (u+a+a)=count T (u+a)+R.card at s
  rw [show u+a+a=u+2*a by omega] at s
  change count T (u+2*a)=count T (u+a)+R.card at s
  have cw : C.card ≤ w := block_card_le T L w
  change w+D=2*C.card at disc
  omega


end GreenFGY
open GreenFGY Finset

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1.H2 := by
  intro T a u L w D apos amin sep hw short hL hR disc dbl failed
  let P := T.filter (· < u+a)
  have pack := difference_packing (u:=u) apos amin sep
  change (sums P (reverse P (u+a))).card+2*count T u ≤ 2*u at pack
  change 4*P.card ≤ (sums P (reverse P (u+a))).card+2*D at dbl
  have mass : count T u+2*count T (u+a) ≤ u+D := by
    change count T u+2*P.card ≤ u+D
    omega
  exact ⟨mass,forced_gap hw short hL hR sep disc mass failed,
    fun _ ht _ hv => first_gap_width hw short hL hR sep disc mass failed ht hv⟩

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H2

section FoldGR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1

/- Integer forms of the discrepancy estimates of Franchi, Gowers and Yip,
arXiv:2607.06073, Sections 4.5–4.8. These locate the maximum between
two successive multiples of the minimum, with a second gap and a
quantitative lower bound on mass just before the maximum. -/
namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1_H3_R1

open Finset

/-- Every interval of a separated set obeys a difference-count bound. -/
def H1 : Prop := ∀ (T : Finset ℕ) (U D : ℕ), (∀ x ∈ T,0 < x) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    (∀ s n : ℕ, s+n ≤ U → 2*(T.filter (fun x => s ≤ x ∧ x < s+n)).card ≤ n+D) →
    ∀ p q : ℕ, p ≤ q → q ≤ U → 2*(T.filter (· < q)).card+(T.filter (· < (q-p))).card ≤ q-p+D+2*(T.filter (· < p)).card

/-- A failed three-prefix bound forces two large gaps and a localized discrepancy maximum. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a u L w D : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ x ∈ T,a ≤ x) → 2*a < L → L < u → L+w < u+a → L ∈ T → L+w-1 ∈ T →
    w < a → 0 < w → (∀ s n : ℕ, s+n ≤ u+2*a → 2*(T.filter (fun x => s ≤ x ∧ x < s+n)).card+w ≤ 2*(T.filter (fun x => L ≤ x ∧ x < L+w)).card+n) →
    w+D=2*(T.filter (fun x => L ≤ x ∧ x < L+w)).card →
    (T.filter (· < u)).card+2*(T.filter (· < (u+a))).card ≤ u+D →
    (∀ t ∈ T,t+L < u+a ∨ u+2*a < t+L+w) →
    (∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    (∀ p q : ℕ, p ≤ q → q ≤ u+2*a → 2*(T.filter (· < q)).card+(T.filter (· < (q-p))).card ≤ q-p+D+2*(T.filter (· < p)).card) →
    u+a ≤ (T.filter (· < u)).card+(T.filter (· < (u+a))).card+(T.filter (· < (u+2*a))).card →
    ∃ g c z : ℕ, L+a<u ∧ u<L+a+w ∧ a<2*D ∧ c ∈ T ∧ c+L<u+a ∧
      (∀ x ∈ T,x+L<u+a → x≤c) ∧ (∀ x ∈ T, c<x → c+a+2<x) ∧
      z ∈ T ∧ u≤z ∧ z<u+a ∧ z+a<c+(L+w) ∧
      (∀ x ∈ T,x<u+a → x≤z) ∧ (∀ x ∈ T,z<x → z+a+2<x) ∧
      2*(T.filter (· < (u-L))).card+(T.filter (· < u)).card+g=u-L-a+(T.filter (· < (L+a))).card ∧
      5*a+2*g+4*(T.filter (· < (u-L))).card≤5*D+4*(T.filter (· < (u+2*a-L))).card ∧
      a+g+2*w+(T.filter (· < (L-2*a))).card+2≤2*D+(T.filter (· < L)).card+(T.filter (fun x => L ≤ x ∧ x < L+w)).card

/-- Configurations surviving both gaps and the localized bounds. -/
def H3 : Prop := ∀ (T : Finset ℕ) (a u L w D : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ x ∈ T,a ≤ x) → 2*a < L → L < u → L+w < u+a → L ∈ T → L+w-1 ∈ T →
    w < a → 0 < w → (∀ s n : ℕ, s+n ≤ u+2*a → 2*(T.filter (fun x => s ≤ x ∧ x < s+n)).card+w ≤ 2*(T.filter (fun x => L ≤ x ∧ x < L+w)).card+n) →
    w+D=2*(T.filter (fun x => L ≤ x ∧ x < L+w)).card →
    (T.filter (· < u)).card+2*(T.filter (· < (u+a))).card ≤ u+D →
    (∀ t ∈ T,t+L < u+a ∨ u+2*a < t+L+w) →
    (∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    (∀ p q : ℕ, p ≤ q → q ≤ u+2*a → 2*(T.filter (· < q)).card+(T.filter (· < (q-p))).card ≤ q-p+D+2*(T.filter (· < p)).card) →
    ∀ g c z : ℕ, (L+a<u ∧ u<L+a+w ∧ a<2*D ∧ c ∈ T ∧ c+L<u+a ∧
      (∀ x ∈ T,x+L<u+a → x≤c) ∧ (∀ x ∈ T, c<x → c+a+2<x) ∧
      z ∈ T ∧ u≤z ∧ z<u+a ∧ z+a<c+(L+w) ∧
      (∀ x ∈ T,x<u+a → x≤z) ∧ (∀ x ∈ T,z<x → z+a+2<x) ∧
      2*(T.filter (· < (u-L))).card+(T.filter (· < u)).card+g=u-L-a+(T.filter (· < (L+a))).card ∧
      5*a+2*g+4*(T.filter (· < (u-L))).card≤5*D+4*(T.filter (· < (u+2*a-L))).card ∧
      a+g+2*w+(T.filter (· < (L-2*a))).card+2≤2*D+(T.filter (· < L)).card+(T.filter (fun x => L ≤ x ∧ x < L+w)).card) →
    (T.filter (· < u)).card+(T.filter (· < (u+a))).card+(T.filter (· < (u+2*a))).card < u+a

theorem main : H1 → H2 → H3 → OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1.H3 := by
  intro windows force remaining T a u L w D ha hu hs bounds sep ha7 _dense _initial _offsets
    _wide _many _gaps _crowded _forced hl lu inside hw short hL hR best _anchor _reflected
    _pos eq mass gap width
  have amin (x : ℕ) (hx : x ∈ T) := (bounds x hx).1
  have dif := windows T (u+2*a) D (fun x hx => Nat.lt_of_lt_of_le (by omega) (amin x hx)) sep (by
    intro p n h
    have bound := best p n h
    omega)
  by_contra! failure
  obtain ⟨g,c,z,conditions⟩ := force T a u L w D ha hu hs amin hl lu inside hL hR short hw
    best eq mass gap width sep dif failure
  exact (not_lt_of_ge failure) (remaining T a u L w D ha hu hs amin hl lu inside hL hR short hw
    best eq mass gap width sep dif g c z conditions)

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1_H3_R1

end FoldGR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H1

/- Original Lean formalization of Franchi–Gowers–Yip, arXiv:2607.06073.
The integer proofs use half-open windows and the two offsets from adding
unit cells. -/
namespace GreenFGY

open Finset
open scoped Pointwise

def count (A : Finset ℕ) (n : ℕ) := (A.filter (· < n)).card
def half (A : Finset ℕ) := A.image (2*·) ∪ A.image (fun i => 2*i+1)

theorem mem_half {A : Finset ℕ} {z : ℕ} :
    z ∈ half A ↔ ∃ x ∈ A, z=2*x ∨ z=2*x+1 := by
  simp only [half,mem_union,mem_image]
  constructor
  · rintro (⟨x,hx,h⟩ | ⟨x,hx,h⟩)
    · exact ⟨x,hx,Or.inl h.symm⟩
    · exact ⟨x,hx,Or.inr h.symm⟩
  · rintro ⟨x,hx,h | h⟩
    · exact Or.inl ⟨x,hx,h.symm⟩
    · exact Or.inr ⟨x,hx,h.symm⟩

private theorem half_count (A : Finset ℕ) (n e : ℕ) (he : e ≤ 1) :
    count (half A) (2*n+e) = count A (n+e) + count A n := by
  let P := (A.filter (· < n+e)).image (2*·)
  let Q := (A.filter (· < n)).image (fun i => 2*i+1)
  have eq : (half A).filter (· < 2*n+e) = P ∪ Q := by
    ext z
    simp only [mem_filter,mem_half,P,Q,mem_union,mem_image]
    constructor
    · rintro ⟨⟨x,hx,h | h⟩,hl⟩
      · exact Or.inl ⟨x,⟨hx,by omega⟩,h.symm⟩
      · exact Or.inr ⟨x,⟨hx,by omega⟩,h.symm⟩
    · rintro (⟨x,⟨hx,hl⟩,h⟩ | ⟨x,⟨hx,hl⟩,h⟩)
      · exact ⟨⟨x,hx,Or.inl h.symm⟩,by omega⟩
      · exact ⟨⟨x,hx,Or.inr h.symm⟩,by omega⟩
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z hz hq
    obtain ⟨x,_,h1⟩ := mem_image.mp hz
    obtain ⟨y,_,h2⟩ := mem_image.mp hq
    omega
  have cp : P.card = count A (n+e) := card_image_of_injective _ (by intro x y h; dsimp at h; omega)
  have cq : Q.card = count A n := card_image_of_injective _ (by intro x y h; dsimp at h; omega)
  unfold count
  rw [eq,card_union_of_disjoint dis,cp,cq]
  rfl

private theorem reflect_before (A B : Finset ℕ) {n q : ℕ} (hq : q ≤ n)
    (noAdd : ∀ x ∈ A, ∀ y ∈ B, x+y+1 ≠ n) :
    count A q + count B n ≤ q+count B (n-q) := by
  let P := A.filter (· < q)
  let U := B.filter (fun y => n-q ≤ y ∧ y < n)
  let Q := U.image (fun y => n-1-y)
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro x hx hxQ
    obtain ⟨y,hy,he⟩ := mem_image.mp hxQ
    obtain ⟨hyB,yl,yr⟩ := mem_filter.mp hy
    exact noAdd x (mem_filter.mp hx).1 y hyB (by omega)
  have sub : P ∪ Q ⊆ range q := by
    intro x hx
    rcases mem_union.mp hx with hp | hQ
    · exact mem_range.mpr (mem_filter.mp hp).2
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hQ
      obtain ⟨_,yl,yr⟩ := mem_filter.mp hy
      exact mem_range.mpr (by omega)
  have cq : Q.card=U.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    have hxn := (mem_filter.mp hx).2.2
    have hyn := (mem_filter.mp hy).2.2
    change n-1-x=n-1-y at e
    omega
  have he : B.filter (· < n) = B.filter (· < n-q) ∪ U := by
    ext x
    simp only [U,mem_filter,mem_union]
    by_cases hx : x ∈ B
    · simp only [hx,true_and]
      omega
    · simp only [hx,false_and,false_or]
  have hd : Disjoint (B.filter (· < n-q)) U := by
    apply disjoint_left.mpr
    intro y ha hb
    exact (not_lt_of_ge (mem_filter.mp hb).2.1) (mem_filter.mp ha).2
  have hh := card_le_card sub
  rw [card_union_of_disjoint dis,card_range,cq] at hh
  change count A q + U.card ≤ q at hh
  have ef : count B n = count B (n-q)+U.card := by rw [count,he,card_union_of_disjoint hd]; rfl
  omega

/-- Two balanced prefixes, with the first ending at a height that bounds
all heights of the second, cover the entire second prefix after addition
of the two possible cell-endpoint offsets. -/
theorem prefix_sum_coverage (A B : Finset ℕ) {m N h : ℕ}
    (hA : ∀ i ≤ m, i ≤ 2*count A i) (peak : 2*count A m = m+h)
    (hB : ∀ i ≤ N, i ≤ 2*count B i ∧ 2*count B i ≤ i+h)
    (k : ℕ) (hk : k < N) : k ∈ (A+B)+range 2 := by
  by_contra missing
  have noAdd (x : ℕ) (hx : x ∈ half A) (y : ℕ) (hy : y ∈ half B) : x+y+1 ≠ 2*k+1 := by
    intro he
    obtain ⟨i,hi,e1⟩ := mem_half.mp hx
    obtain ⟨j,hj,e2⟩ := mem_half.mp hy
    have either : k=i+j ∨ k=i+j+1 := by omega
    have hsum := mem_add.mpr ⟨i,hi,j,hj,rfl⟩
    apply missing
    rcases either with eq | eq
    · exact mem_add.mpr ⟨i+j,hsum,0,by decide,by omega⟩
    · exact mem_add.mpr ⟨i+j,hsum,1,by decide,by omega⟩
  obtain ⟨b0,_⟩ := hB k (by omega)
  obtain ⟨b1,_⟩ := hB (k+1) (by omega)
  by_cases km : k < m
  · have hc := reflect_before (half A) (half B) (q:=2*k+1) (le_refl _) noAdd
    rw [Nat.sub_self,show count (half B) 0=0 by simp [count],add_zero,
      half_count A k 1 (by decide),half_count B k 1 (by decide)] at hc
    have a0 := hA k (by omega)
    have a1 := hA (k+1) (by omega)
    omega
  · let r := k-m
    have er : r+m=k := Nat.sub_add_cancel (by omega)
    obtain ⟨_,br0⟩ := hB r (by omega)
    obtain ⟨_,br1⟩ := hB (r+1) (by omega)
    have hc := reflect_before (half A) (half B) (q:=2*m) (by omega) noAdd
    have ea := half_count A m 0 (by decide)
    simp only [add_zero] at ea
    rw [ea,half_count B k 1 (by decide),show 2*k+1-2*m=2*r+1 by omega,
      half_count B r 1 (by decide)] at hc
    omega



open Finset
open scoped Pointwise

theorem count_zero (A : Finset ℕ) : count A 0 = 0 := by simp [count]

theorem count_succ (A : Finset ℕ) (j : ℕ) :
    count A (j+1) = count A j + if j ∈ A then 1 else 0 := by
  classical
  by_cases hit : j ∈ A
  · have eq : A.filter (· < j+1) = insert j (A.filter (· < j)) := by
      ext z
      simp only [mem_filter,mem_insert]
      constructor
      · rintro ⟨hz,hl⟩
        by_cases ze : z=j
        · exact Or.inl ze
        · exact Or.inr ⟨hz,by omega⟩
      · rintro (rfl|⟨hz,hl⟩)
        · exact ⟨hit,by omega⟩
        · exact ⟨hz,by omega⟩
    unfold count
    rw [eq,card_insert_of_notMem (by simp),if_pos hit]
  · have eq : A.filter (· < j+1) = A.filter (· < j) := by
      ext z
      simp only [mem_filter]
      constructor
      · rintro ⟨hz,hl⟩
        have zn : z ≠ j := fun e => hit (e ▸ hz)
        exact ⟨hz,by omega⟩
      · rintro ⟨hz,hl⟩
        exact ⟨hz,by omega⟩
    unfold count
    rw [eq,if_neg hit,Nat.add_zero]

/-- The initial balanced excursion in the path with rises on members and
falls on missing integers. The given height occurs at a prefix of length k. -/
structure Excursion (A : Finset ℕ) (m h : ℕ) : Prop where
  ends : 2*count A m = m
  gap : m ∉ A
  bounds : ∀ i ≤ m, i ≤ 2*count A i ∧ 2*count A i ≤ i+h
  peak : ∃ k ≤ m, 2*count A k = k+h

theorem exists_excursion (A : Finset ℕ) : ∃ m h, Excursion A m h := by
  classical
  have stop : ∃ j, 2*count A j < j := by
    refine ⟨2*A.card+1,?_⟩
    have c : count A (2*A.card+1) ≤ A.card := card_filter_le _ _
    omega
  let s := Nat.find stop
  have fail : 2*count A s < s := Nat.find_spec stop
  have init (i : ℕ) (hi : i < s) : i ≤ 2*count A i :=
    Nat.le_of_not_gt (Nat.find_min stop hi)
  have spos : 0 < s := by omega
  let m := s-1
  have ms : m+1=s := by dsimp [m]; omega
  have base := init m (by omega)
  have step := count_succ A m
  rw [ms] at step
  have gap : m ∉ A := by
    intro hit
    rw [if_pos hit] at step
    omega
  rw [if_neg gap] at step
  have ends : 2*count A m = m := by omega
  let levels := (range (m+1)).image (fun i => 2*count A i-i)
  have nz : levels.Nonempty := ⟨_,mem_image.mpr ⟨0,mem_range.mpr (by omega),rfl⟩⟩
  let h := levels.max' nz
  obtain ⟨k,hk,eq⟩ := mem_image.mp (max'_mem levels nz)
  have kl : k < m+1 := mem_range.mp hk
  have kb := init k (by omega)
  have top : 2*count A k-k=h := eq
  refine ⟨m,h,ends,gap,?_,k,by omega,by omega⟩
  intro i hi
  have ib := init i (by omega)
  have le : 2*count A i-i ≤ h := le_max' levels _ (mem_image.mpr ⟨i,mem_range.mpr (by omega),rfl⟩)
  exact ⟨ib,by omega⟩

theorem excursion_nonempty {A : Finset ℕ} {m h : ℕ} (head : Excursion A m h)
    (begins : 0 ∈ A) : 0 < m ∧ 0 < h ∧ 0 < count A m := by
  have hm : 0 < m := by
    by_contra! hz
    exact head.gap (by simpa [show m=0 by omega] using begins)
  have one := count_succ A 0
  rw [count_zero,if_pos begins] at one
  have bound := (head.bounds 1 (by omega)).2
  have endBound := head.ends
  change count A 1 = 1 at one
  exact ⟨hm,by omega,by omega⟩

theorem excursion_sum_coverage (A B : Finset ℕ) {m n d e : ℕ}
    (left : Excursion A m d) (right : Excursion B n e) (le : e ≤ d) (k : ℕ) (hk : k<n) :
    k ∈ (A+B)+range 2 := by
  obtain ⟨x,hx,peak⟩ := left.peak
  refine prefix_sum_coverage A B (m:=x) (N:=n) (h:=d) (fun i hi => (left.bounds i (hi.trans hx)).1)
    peak (fun i hi => ?_) k hk
  obtain ⟨pos,neg⟩ := right.bounds i hi
  exact ⟨pos,by omega⟩



open Finset
open scoped Pointwise

def tail (A : Finset ℕ) (p : ℕ) := (A.filter (p ≤ ·)).image (·-p)

theorem mem_tail {A : Finset ℕ} {p x : ℕ} : x ∈ tail A p ↔ p+x ∈ A := by
  constructor
  · intro hit
    obtain ⟨y,hy,e⟩ := mem_image.mp hit
    obtain ⟨hy,lo⟩ := mem_filter.mp hy
    have eq : p+x=y := by change y-p=x at e; omega
    rwa [eq]
  · intro hit
    exact mem_image.mpr ⟨p+x,mem_filter.mpr ⟨hit,by omega⟩,by omega⟩

theorem tail_count (A : Finset ℕ) (p n : ℕ) :
    count (tail A p) n = (A.filter (fun x => p ≤ x ∧ x < p+n)).card := by
  let U := A.filter (fun x => p ≤ x ∧ x < p+n)
  have eq : (tail A p).filter (· < n) = U.image (·-p) := by
    ext x
    constructor
    · intro h
      obtain ⟨hx,lt⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨p+x,mem_filter.mpr ⟨mem_tail.mp hx,by omega,by omega⟩,by omega⟩
    · intro h
      obtain ⟨y,hy,e⟩ := mem_image.mp h
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hy
      change y-p=x at e
      exact mem_filter.mpr ⟨mem_tail.mpr (by rwa [show p+x=y by omega]),by omega⟩
  unfold count
  rw [eq]
  apply card_image_of_injOn
  intro x hx y hy he
  have xl := (mem_filter.mp hx).2.1
  have yl := (mem_filter.mp hy).2.1
  change x-p=y-p at he
  omega

/-- Every interval has discrepancy at most D. -/
def Capped (A : Finset ℕ) (D : ℕ) : Prop := ∀ p n, 2*count (tail A p) n ≤ n+D

theorem capped_mono {A B : Finset ℕ} {D : ℕ} (sub : A ⊆ B) (h : Capped B D) :
    Capped A D := by
  intro p n
  have z := h p n
  rw [tail_count] at z ⊢
  have k := card_le_card (filter_subset_filter (fun x : ℕ => p ≤ x ∧ x < p+n) sub)
  omega

theorem lift_sum {A B : Finset ℕ} {b k : ℕ} (h : k ∈ (A+tail B b)+range 2) :
    b+k ∈ (A+B)+range 2 := by
  obtain ⟨t,ht,e,he,eq⟩ := mem_add.mp h
  obtain ⟨i,hi,j,hj,et⟩ := mem_add.mp ht
  exact mem_add.mpr ⟨i+(b+j),mem_add.mpr ⟨i,hi,b+j,mem_tail.mp hj,rfl⟩,e,he,by omega⟩

theorem anchored_sum (A : Finset ℕ) {m D : ℕ}
    (balance : ∀ i ≤ m, i ≤ 2*count A i) (peak : 2*count A m=m+D)
    (B : Finset ℕ) (M : ℕ) (capped : Capped B D) (bounded : ∀ x ∈ B, x < M) :
    2*B.card ≤ (((A+B)+range 2).filter (· < M+D)).card := by
  classical
  induction hN : B.card using Nat.strong_induction_on generalizing B with
  | h N ih =>
    by_cases empty : B = ∅
    · have z : N=0 := by simpa [empty] using hN.symm
      simp [z]
    have ne := nonempty_iff_ne_empty.mpr empty
    let b := B.min' ne
    have hb : b ∈ B := min'_mem B ne
    have low (x : ℕ) (hx : x ∈ B) : b ≤ x := min'_le B x hx
    obtain ⟨n,e,head⟩ := exists_excursion (tail B b)
    have starts : 0 ∈ tail B b := mem_tail.mpr (by simpa using hb)
    obtain ⟨hn,_,hcount⟩ := excursion_nonempty head starts
    obtain ⟨k,_,hp⟩ := head.peak
    have cap := capped b k
    have hD : e ≤ D := by omega
    let U := B.filter (· < b+n)
    let V := B.filter (b+n ≤ ·)
    have cu : count (tail B b) n = U.card := by
      rw [tail_count]
      congr 1
      ext x
      simp only [U,mem_filter]
      exact ⟨fun ⟨hit,_,hi⟩ => ⟨hit,hi⟩,fun ⟨hit,hi⟩ => ⟨hit,low x hit,hi⟩⟩
    have partition : U.card+V.card=B.card := by
      have part := card_filter_add_card_filter_not (s:=B) (fun x => x < b+n)
      simpa only [U,V,not_lt] using part
    have less : V.card < N := by omega
    have sub : V ⊆ B := filter_subset _ _
    have other := ih V.card less V (capped_mono sub capped) (fun x hx => bounded x (sub hx)) rfl
    have bound_n : b+n ≤ M+D := by
      by_contra! large
      have src := capped b (M-b)
      have full : count (tail B b) (M-b)=count (tail B b) n := by
        unfold count
        congr 1
        ext x
        simp only [mem_filter,mem_tail]
        constructor
        · rintro ⟨hit,hi⟩
          exact ⟨hit,by omega⟩
        · rintro ⟨hit,hi⟩
          have h := bounded (b+x) hit
          exact ⟨hit,by omega⟩
      rw [full,head.ends] at src
      have bm := bounded b hb
      omega
    let S := ((A+V)+range 2).filter (· < M+D)
    let K := Ico b (b+n)
    have sep : Disjoint K S := by
      apply disjoint_left.mpr
      intro x hk hs
      have hi := (mem_Ico.mp hk).2
      obtain ⟨t,ht,z,_,he⟩ := mem_add.mp (mem_filter.mp hs).1
      obtain ⟨i,_,j,hj,eq⟩ := mem_add.mp ht
      have lo := (mem_filter.mp hj).2
      omega
    have all : K ∪ S ⊆ ((A+B)+range 2).filter (· < M+D) := by
      intro x hx
      rcases mem_union.mp hx with hk|hs
      · obtain ⟨lo,up⟩ := mem_Ico.mp hk
        have cov := prefix_sum_coverage A (tail B b) (N:=n) balance peak
          (fun i hi => ⟨(head.bounds i hi).1,(head.bounds i hi).2.trans (by omega)⟩)
          (x-b) (by omega)
        have lifted := lift_sum cov
        have eq : b+(x-b)=x := by omega
        exact mem_filter.mpr ⟨eq ▸ lifted,by omega⟩
      · obtain ⟨hit,lt⟩ := mem_filter.mp hs
        obtain ⟨t,ht,e,he,eq⟩ := mem_add.mp hit
        obtain ⟨i,hi,j,hj,et⟩ := mem_add.mp ht
        exact mem_filter.mpr ⟨mem_add.mpr ⟨t,mem_add.mpr ⟨i,hi,j,sub hj,et⟩,e,he,eq⟩,lt⟩
    have final := card_le_card all
    rw [card_union_of_disjoint sep] at final
    have ck : K.card=n := by simp [K]
    have endcard := head.ends
    change 2*V.card ≤ S.card at other
    omega



open Finset
open scoped Pointwise

theorem tail_zero (A : Finset ℕ) : tail A 0=A := by ext x; simp [mem_tail]
theorem tail_tail (A : Finset ℕ) (p j : ℕ) : tail (tail A p) j=tail A (p+j) := by
  ext x
  simp only [mem_tail,Nat.add_assoc]

theorem count_split (A : Finset ℕ) (p n : ℕ) :
    count A (p+n)=count A p+count (tail A p) n := by
  rw [tail_count]
  have split : A.filter (· < p+n) =
      A.filter (· < p) ∪ A.filter (fun x => p ≤ x ∧ x < p+n) := by
    ext x
    simp only [mem_filter,mem_union]
    constructor
    · rintro ⟨hit,hi⟩
      by_cases lo : x < p
      · exact Or.inl ⟨hit,lo⟩
      · exact Or.inr ⟨hit,by omega,hi⟩
    · rintro (⟨hit,lo⟩|⟨hit,lo,hi⟩) <;> exact ⟨hit,by omega⟩
  have dis : Disjoint (A.filter (· < p)) (A.filter (fun x => p ≤ x ∧ x < p+n)) := by
    apply disjoint_left.mpr
    intro x hl hr
    exact (not_lt_of_ge (mem_filter.mp hr).2.1) (mem_filter.mp hl).2
  unfold count
  rw [split,card_union_of_disjoint dis]

theorem cap_tail {A : Finset ℕ} {D : ℕ} (h : Capped A D) (j : ℕ) :
    Capped (tail A j) D := by
  intro p n
  rw [tail_tail]
  exact h _ _

def Reaches (A : Finset ℕ) (D : ℕ) : Prop :=
  ∃ p n, n+D ≤ 2*count (tail A p) n

theorem reaches_tail_after_excursion {A : Finset ℕ} {D m h : ℕ}
    (big : Reaches A D) (head : Excursion A m h) (small : h<D) : Reaches (tail A m) D := by
  obtain ⟨p,n,rise⟩ := big
  by_cases pm : m ≤ p
  · refine ⟨p-m,n,?_⟩
    rwa [tail_tail,show m+(p-m)=p by omega]
  have diff := count_split A p n
  have ppos := (head.bounds p (by omega)).1
  have behind : m ≤ p+n := by
    by_contra! early
    have cap := (head.bounds (p+n) early.le).2
    omega
  refine ⟨0,p+n-m,?_⟩
  rw [tail_zero]
  have diff' := count_split A m (p+n-m)
  rw [show m+(p+n-m)=p+n by omega] at diff'
  have endval := head.ends
  omega

theorem reaches_normalize {A : Finset ℕ} {D b : ℕ}
    (positive : 0<D) (big : Reaches A D) (lower : ∀ x ∈ A, b ≤ x) : Reaches (tail A b) D := by
  obtain ⟨p,n,rise⟩ := big
  by_cases pb : b ≤ p
  · refine ⟨p-b,n,?_⟩
    rwa [tail_tail,show b+(p-b)=p by omega]
  have zero (j : ℕ) (hj : j ≤ b) : count A j=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h1 := (mem_filter.mp hx).2
    have h2 := lower x (mem_filter.mp hx).1
    omega
  have d := count_split A p n
  have zp := zero p (by omega)
  have endpos : b ≤ p+n := by
    by_contra! prior
    have z := zero (p+n) prior.le
    omega
  refine ⟨0,p+n-b,?_⟩
  rw [tail_zero]
  have d' := count_split A b (p+n-b)
  rw [show b+(p+n-b)=p+n by omega] at d'
  have zb := zero b le_rfl
  omega

theorem tail_card (A : Finset ℕ) (b : ℕ) : (tail A b).card=(A.filter (b ≤ ·)).card := by
  apply card_image_of_injOn
  intro x hx y hy e
  have xl := (mem_filter.mp hx).2
  have yl := (mem_filter.mp hy).2
  change x-b=y-b at e
  omega

theorem normalize_card {A : Finset ℕ} {b : ℕ} (lower : ∀ x ∈ A,b ≤ x) : (tail A b).card=A.card := by
  rw [tail_card,filter_eq_self.mpr lower]

def reverse (A : Finset ℕ) (M : ℕ) := A.image (M-·)

theorem mem_reverse {A : Finset ℕ} {M x : ℕ} (bound : ∀ y ∈ A, y ≤ M) :
    x ∈ reverse A M ↔ x ≤ M ∧ M-x ∈ A := by
  constructor
  · intro hit
    obtain ⟨y,hy,e⟩ := mem_image.mp hit
    change M-y=x at e
    have lim := bound y hy
    exact ⟨by omega,by rwa [show M-x=y by omega]⟩
  · rintro ⟨lo,hit⟩
    exact mem_image.mpr ⟨M-x,hit,by omega⟩

theorem reverse_card {A : Finset ℕ} {M : ℕ} (bound : ∀ y ∈ A,y ≤ M) :
    (reverse A M).card=A.card := by
  apply card_image_of_injOn
  intro x hx y hy e
  have xl := bound x hx; have yl := bound y hy
  change M-x=M-y at e
  omega

theorem reverse_inv {A : Finset ℕ} {M : ℕ} (bound : ∀ y ∈ A,y ≤ M) :
    reverse (reverse A M) M=A := by
  have rhs (y : ℕ) (hy : y ∈ reverse A M) := (mem_reverse bound |>.mp hy).1
  ext x
  rw [mem_reverse rhs,mem_reverse bound]
  constructor
  · rintro ⟨lo,_,hit⟩
    rwa [show M-(M-x)=x by omega] at hit
  · intro hit
    have xl := bound x hit
    exact ⟨xl,by omega,by rwa [show M-(M-x)=x by omega]⟩

theorem reverse_prefix {A : Finset ℕ} {M : ℕ} (bound : ∀ y ∈ A,y ≤ M)
    {p n : ℕ} (inside : p+n ≤ M+1) :
    count (tail (reverse A M) p) n = count (tail A (M+1-(p+n))) n := by
  rw [tail_count,tail_count]
  let U := A.filter (fun x => M+1-(p+n) ≤ x ∧ x < M+1-(p+n)+n)
  have e : (reverse A M).filter (fun x => p ≤ x ∧ x < p+n) = reverse U M := by
    ext x
    rw [mem_filter,mem_reverse bound,mem_reverse (fun y hy => bound y (mem_filter.mp hy).1)]
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨lo,hit⟩,left,right⟩
      exact ⟨lo,hit,by omega,by omega⟩
    · rintro ⟨lo,hit,left,right⟩
      exact ⟨⟨lo,hit⟩,by omega,by omega⟩
  rw [e,reverse_card (fun y hy => bound y (mem_filter.mp hy).1)]

theorem count_clip {A : Finset ℕ} {M : ℕ} (bound : ∀ y ∈ A,y ≤ M) (p n : ℕ) :
    count (tail A p) n = count (tail A p) (min n (M+1-p)) := by
  rw [tail_count,tail_count]
  congr 1
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hit,lo,hi⟩
    have max := bound x hit
    exact ⟨hit,lo,by omega⟩
  · rintro ⟨hit,lo,hi⟩
    exact ⟨hit,lo,by omega⟩

theorem cap_reverse {A : Finset ℕ} {M D : ℕ} (bound : ∀ y ∈ A,y ≤ M) (cap : Capped A D) :
    Capped (reverse A M) D := by
  have bound' (y : ℕ) (hy : y ∈ reverse A M) := (mem_reverse bound |>.mp hy).1
  intro p n
  rw [count_clip bound' p n]
  by_cases high : M+1<p
  · simp [show M+1-p=0 by omega,count_zero]
  rw [reverse_prefix bound (by omega)]
  have c := cap (M+1-(p+min n (M+1-p))) (min n (M+1-p))
  omega

theorem reaches_reverse {A : Finset ℕ} {M D : ℕ} (bound : ∀ y ∈ A,y ≤ M)
    (pos : 0<D) (big : Reaches A D) : Reaches (reverse A M) D := by
  obtain ⟨p,n,rise⟩ := big
  let w := min n (M+1-p)
  have orig := count_clip bound p n
  change count (tail A p) n = count (tail A p) w at orig
  have wpos : 0<w := by
    by_contra! hp
    have wz : w=0 := by omega
    rw [wz,count_zero] at orig
    omega
  have wl : p+w ≤ M+1 := by dsimp [w] at *; omega
  have wn : w ≤ n := min_le_left _ _
  refine ⟨M+1-(p+w),w,?_⟩
  rw [reverse_prefix bound (by omega),show M+1-(M+1-(p+w)+w)=p by omega]
  omega



open Finset
open scoped Pointwise

def sums (A B : Finset ℕ) := (A+B)+range 2

theorem mem_sums {A B : Finset ℕ} {t : ℕ} :
    t ∈ sums A B ↔ ∃ x ∈ A, ∃ y ∈ B, ∃ e ≤ 1,x+y+e=t := by
  constructor
  · intro hit
    obtain ⟨s,hs,e,he,rfl⟩ := mem_add.mp hit
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hs
    exact ⟨x,hx,y,hy,e,by have z := mem_range.mp he; omega,rfl⟩
  · rintro ⟨x,hx,y,hy,e,he,rfl⟩
    exact mem_add.mpr ⟨x+y,mem_add.mpr ⟨x,hx,y,hy,rfl⟩,e,mem_range.mpr (by omega),rfl⟩

theorem sums_comm (A B : Finset ℕ) : sums A B=sums B A := by unfold sums; rw [add_comm A B]

theorem normalize_sums {A B : Finset ℕ} {a b : ℕ} (loA : ∀x ∈ A,a ≤ x)
    (loB : ∀x ∈ B,b ≤ x) : (sums (tail A a) (tail B b)).card = (sums A B).card := by
  let U := sums (tail A a) (tail B b)
  have eq : U.image (fun x => a+b+x)=sums A B := by
    ext t
    constructor
    · intro h
      obtain ⟨z,hz,e⟩ := mem_image.mp h
      obtain ⟨x,hx,y,hy,k,hk,et⟩ := mem_sums.mp hz
      exact mem_sums.mpr ⟨a+x,mem_tail.mp hx,b+y,mem_tail.mp hy,k,hk,by omega⟩
    · intro h
      obtain ⟨x,hx,y,hy,k,hk,e⟩ := mem_sums.mp h
      have xl := loA x hx
      have yl := loB y hy
      exact mem_image.mpr ⟨x-a+(y-b)+k,mem_sums.mpr
        ⟨x-a,mem_tail.mpr (by rwa [show a+(x-a)=x by omega]),
         y-b,mem_tail.mpr (by rwa [show b+(y-b)=y by omega]),k,hk,rfl⟩,by omega⟩
  have card := card_image_of_injective U (add_right_injective (a+b))
  rwa [eq,eq_comm] at card

theorem sums_bound {A B : Finset ℕ} {M N : ℕ} (ha : ∀x ∈ A,x ≤ M) (hb : ∀y ∈ B,y ≤ N)
    {x : ℕ} (hx : x ∈ sums A B) : x ≤ M+N+1 := by
  obtain ⟨i,hi,j,hj,k,hk,e⟩ := mem_sums.mp hx
  have ai := ha i hi; have bj := hb j hj
  omega

theorem reverse_sums {A B : Finset ℕ} {M N : ℕ}
    (ha : ∀x ∈ A,x ≤ M) (hb : ∀y ∈ B,y ≤ N) :
    sums (reverse A M) (reverse B N)=reverse (sums A B) (M+N+1) := by
  ext t
  rw [mem_reverse (fun _ hx => sums_bound ha hb hx)]
  constructor
  · intro hit
    obtain ⟨i,hi,j,hj,e,he,eq⟩ := mem_sums.mp hit
    obtain ⟨il,ai⟩ := (mem_reverse ha).mp hi
    obtain ⟨jl,bj⟩ := (mem_reverse hb).mp hj
    exact ⟨by omega,mem_sums.mpr ⟨M-i,ai,N-j,bj,1-e,by omega,by omega⟩⟩
  · rintro ⟨tl,hit⟩
    obtain ⟨i,hi,j,hj,e,he,eq⟩ := mem_sums.mp hit
    have il := ha i hi
    have jl := hb j hj
    exact mem_sums.mpr ⟨M-i,mem_image.mpr ⟨i,hi,rfl⟩,N-j,mem_image.mpr ⟨j,hj,rfl⟩,
      1-e,by omega,by omega⟩

def Bound (A B : Finset ℕ) (D : ℕ) : Prop := 2*A.card+2*B.card ≤ (sums A B).card+2*D

theorem opposite_anchors {A B : Finset ℕ} {M N D m n : ℕ}
    (ha : ∀x ∈ A,x ≤ M) (hb : ∀y ∈ B,y ≤ N) (ca : Capped A D) (cb : Capped B D)
    (front : Excursion A m D) (back : Excursion (reverse B N) n D) : Bound A B D := by
  obtain ⟨k,km,pk⟩ := front.peak
  obtain ⟨j,jn,pj⟩ := back.peak
  let S := sums A B
  let P := S.filter (· < N+1+D)
  let Q := S.filter (fun x => N+1 ≤ x+D)
  have left : 2*B.card ≤ P.card := anchored_sum A (fun i hi => (front.bounds i (hi.trans km)).1)
    pk B (N+1) cb (fun x hx => Nat.lt_succ_of_le (hb x hx))
  have right := anchored_sum (reverse B N) (fun i hi => (back.bounds i (hi.trans jn)).1)
    pj (reverse A M) (M+1) (cap_reverse ha ca)
    (fun x hx => Nat.lt_succ_of_le ((mem_reverse ha).mp hx).1)
  change 2*(reverse A M).card ≤ ((sums (reverse B N) (reverse A M)).filter (· < M+1+D)).card at right
  rw [reverse_card ha,sums_comm,reverse_sums ha hb] at right
  have eq : (reverse (sums A B) (M+N+1)).filter (· < M+1+D) = reverse Q (M+N+1) := by
    ext x
    rw [mem_filter,mem_reverse (fun _ hx => sums_bound ha hb hx),
      mem_reverse (fun _ hx => sums_bound ha hb (mem_filter.mp hx).1)]
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨xl,hit⟩,hi⟩
      exact ⟨xl,hit,by omega⟩
    · rintro ⟨xl,hit,hi⟩
      exact ⟨⟨xl,hit⟩,by omega⟩
  rw [eq,reverse_card (fun _ hx => sums_bound ha hb (mem_filter.mp hx).1)] at right
  have overlap : P ∩ Q ⊆ Ico (N+1-D) (N+1+D) := by
    intro x hx
    obtain ⟨hp,hq⟩ := mem_inter.mp hx
    have hi := (mem_filter.mp hp).2; have lo := (mem_filter.mp hq).2
    exact mem_Ico.mpr ⟨by omega,hi⟩
  have cap := card_le_card overlap
  rw [Nat.card_Ico] at cap
  have join : P ∪ Q ⊆ S := union_subset (filter_subset _ _) (filter_subset _ _)
  change 2*A.card ≤ Q.card at right
  have upper := card_le_card join
  have sum := card_union_add_card_inter P Q
  change 2*A.card+2*B.card ≤ S.card+2*D
  omega

def Smaller (N D : ℕ) := ∀ A B : Finset ℕ, A.card+B.card < N → Capped A D → Capped B D →
  Reaches A D → Reaches B D → Bound A B D

theorem bound_comm (A B : Finset ℕ) (D : ℕ) : Bound A B D ↔ Bound B A D := by
  unfold Bound
  rw [sums_comm,add_comm (2*A.card) (2*B.card)]

theorem peel {A B : Finset ℕ} {m n e d D : ℕ}
    (_za : 0 ∈ A) (zb : 0 ∈ B) (a : Excursion A m e) (b : Excursion B n d) (fits : d ≤ e)
    (small : d<D) (ca : Capped A D) (cb : Capped B D) (pa : Reaches A D) (pb : Reaches B D)
    (ih : Smaller (A.card+B.card) D) : Bound A B D := by
  let V := B.filter (n ≤ ·)
  have pv : Reaches V D := by
    obtain ⟨p,w,h⟩ := reaches_tail_after_excursion pb b small
    rw [tail_tail] at h
    have eq : tail V (n+p)=tail B (n+p) := by
      ext x
      simp only [V,mem_tail,mem_filter]
      exact ⟨And.left,fun hit => ⟨hit,by omega⟩⟩
    exact ⟨n+p,w,by rwa [eq]⟩
  have part : count B n+V.card=B.card := by
    simpa only [count,V,not_lt] using card_filter_add_card_filter_not (s:=B) (fun x => x<n)
  have hn := (excursion_nonempty b zb).2.2
  have sub : V ⊆ B := filter_subset _ _
  have smallerResult := ih A V (by omega) ca (capped_mono sub cb) pa pv
  have sep : Disjoint (range n) (sums A V) := by
    apply disjoint_left.mpr
    intro x hx hit
    obtain ⟨i,_,j,hj,k,_,eq⟩ := mem_sums.mp hit
    have lo := (mem_filter.mp hj).2; have hi := mem_range.mp hx
    omega
  have all : range n ∪ sums A V ⊆ sums A B := by
    intro x hx
    rcases mem_union.mp hx with hr|hs
    · exact excursion_sum_coverage A B a b fits x (mem_range.mp hr)
    · obtain ⟨i,hi,j,hj,k,hk,eq⟩ := mem_sums.mp hs
      exact mem_sums.mpr ⟨i,hi,j,sub hj,k,hk,eq⟩
  have lower := card_le_card all
  rw [card_union_of_disjoint sep,card_range] at lower
  have ends := b.ends
  unfold Bound at smallerResult ⊢
  omega

theorem front_alternative {A B : Finset ℕ} {D : ℕ}
    (za : 0 ∈ A) (zb : 0 ∈ B) (ca : Capped A D) (cb : Capped B D)
    (pa : Reaches A D) (pb : Reaches B D) (ih : Smaller (A.card+B.card) D) :
    Bound A B D ∨ (∃ m, Excursion A m D) ∧ ∃ n, Excursion B n D := by
  obtain ⟨m,e,a⟩ := exists_excursion A
  obtain ⟨n,d,b⟩ := exists_excursion B
  obtain ⟨i,_,ha⟩ := a.peak
  obtain ⟨j,_,hb⟩ := b.peak
  have ea := ca 0 i; have eb := cb 0 j
  rw [tail_zero] at ea eb
  by_cases ds : d<D ∧ d≤e
  · exact Or.inl (peel za zb a b ds.2 ds.1 ca cb pa pb ih)
  by_cases es : e<D ∧ e≤d
  · have ih' : Smaller (B.card+A.card) D := by rwa [Nat.add_comm B.card A.card]
    exact Or.inl ((bound_comm A B D).mpr (peel zb za b a es.2 es.1 cb ca pb pa ih'))
  have eD : e=D := by omega
  have dD : d=D := by omega
  exact Or.inr ⟨⟨m,eD ▸ a⟩,n,dD ▸ b⟩

theorem normalized_double {A B : Finset ℕ} {D : ℕ}
    (pos : 0<D) (za : 0 ∈ A) (zb : 0 ∈ B) (ca : Capped A D) (cb : Capped B D)
    (pa : Reaches A D) (pb : Reaches B D) (ih : Smaller (A.card+B.card) D) : Bound A B D := by
  rcases front_alternative za zb ca cb pa pb ih with done|⟨⟨m,pa'⟩,_⟩
  · exact done
  let M := A.max' ⟨0,za⟩
  let N := B.max' ⟨0,zb⟩
  have ha (x : ℕ) (hx : x ∈ A) : x ≤ M := le_max' A x hx
  have hb (x : ℕ) (hx : x ∈ B) : x ≤ N := le_max' B x hx
  have ra : 0 ∈ reverse A M := (mem_reverse ha).mpr ⟨Nat.zero_le _,by simpa using max'_mem A ⟨0,za⟩⟩
  have rb : 0 ∈ reverse B N := (mem_reverse hb).mpr ⟨Nat.zero_le _,by simpa using max'_mem B ⟨0,zb⟩⟩
  have ih' : Smaller ((reverse A M).card+(reverse B N).card) D := by rwa [reverse_card ha,reverse_card hb]
  rcases front_alternative ra rb (cap_reverse ha ca) (cap_reverse hb cb)
    (reaches_reverse ha pos pa) (reaches_reverse hb pos pb) ih' with done|⟨_,⟨n,pb'⟩⟩
  · unfold Bound at done ⊢
    rwa [reverse_card ha,reverse_card hb,reverse_sums ha hb,reverse_card (fun _ hx => sums_bound ha hb hx)] at done
  · exact opposite_anchors ha hb ca cb pa' pb'

/-- Equal maximal discrepancies give a doubling estimate for the cell sumset. -/
theorem discrete_sumset {A B : Finset ℕ} {D : ℕ} (pos : 0<D)
    (ca : Capped A D) (cb : Capped B D) (pa : Reaches A D) (pb : Reaches B D) : Bound A B D := by
  classical
  induction hN : A.card+B.card using Nat.strong_induction_on generalizing A B with
  | h N ih =>
    have nonempty (S : Finset ℕ) (p : Reaches S D) : S.Nonempty := by
      by_contra! empty
      obtain ⟨j,w,h⟩ := p
      rw [empty] at h
      simp [tail,count] at h
      omega
    let a := A.min' (nonempty A pa)
    let b := B.min' (nonempty B pb)
    have a0 : 0 ∈ tail A a := mem_tail.mpr (by simpa using min'_mem A (nonempty A pa))
    have b0 : 0 ∈ tail B b := mem_tail.mpr (by simpa using min'_mem B (nonempty B pb))
    have loA (x : ℕ) (hx : x ∈ A) : a ≤ x := min'_le A x hx
    have loB (x : ℕ) (hx : x ∈ B) : b ≤ x := min'_le B x hx
    have ih' : Smaller ((tail A a).card+(tail B b).card) D := by
      rw [normalize_card loA,normalize_card loB,hN]
      intro T U sm ct cu pt pu
      exact ih _ sm ct cu pt pu rfl
    have res := normalized_double pos a0 b0 (cap_tail ca a) (cap_tail cb b)
      (reaches_normalize pos pa loA) (reaches_normalize pos pb loB) ih'
    unfold Bound at res ⊢
    rwa [normalize_card loA,normalize_card loB,normalize_sums loA loB] at res



open Finset
open scoped Pointwise

theorem interval_difference_packing {T : Finset ℕ} {a u : ℕ} (pos : ∀ x ∈ T,0 < x)
    (sep : ∀ i ∈ T,∀ j ∈ T,∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    let P := T.filter (fun x => a ≤ x ∧ x<u+a)
    (sums P (reverse P (u+a))).card+2*count T u ≤ 2*u := by
  classical
  let M := u+a
  let P := T.filter (fun x => a ≤ x ∧ x<M)
  let R := T.filter (· < u)
  let S := sums P (reverse P M)
  let X := R.image (fun x => M+x)
  let Y := R.image (fun x => M+1-x)
  have bnd (x : ℕ) (hx : x ∈ P) : x ≤ M := (mem_filter.mp hx).2.2.le
  have cx : X.card=R.card := card_image_of_injective _ (add_right_injective M)
  have cy : Y.card=R.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    have xl := (mem_filter.mp hx).2
    have yl := (mem_filter.mp hy).2
    change M+1-x=M+1-y at e
    dsimp [M] at *
    omega
  have xy : Disjoint X Y := by
    apply disjoint_left.mpr
    intro z hx hy
    obtain ⟨i,hi,e⟩ := mem_image.mp hx
    obtain ⟨j,hj,g⟩ := mem_image.mp hy
    have il := pos i (mem_filter.mp hi).1
    have jl := pos j (mem_filter.mp hj).1
    change M+i=z at e
    change M+1-j=z at g
    omega
  have pieces {z : ℕ} (h : z ∈ S) :
      ∃ i ∈ P, ∃ j ∈ P, ∃ e ≤ 1,z+j=M+i+e := by
    obtain ⟨i,hi,k,hk,e,he,eq⟩ := mem_sums.mp h
    obtain ⟨j,hj,hrev⟩ := mem_image.mp hk
    have jl := bnd j hj
    change M-j=k at hrev
    exact ⟨i,hi,j,hj,e,he,by omega⟩
  have free : Disjoint S (X ∪ Y) := by
    apply disjoint_left.mpr
    intro z hs bad
    obtain ⟨i,hi,j,hj,e,he,eq⟩ := pieces hs
    rcases mem_union.mp bad with x|y
    · obtain ⟨d,hd,ev⟩ := mem_image.mp x
      have v := sep j (mem_filter.mp hj).1 d (mem_filter.mp hd).1 i (mem_filter.mp hi).1
      change M+d=z at ev
      omega
    · obtain ⟨d,hd,ev⟩ := mem_image.mp y
      have v := sep i (mem_filter.mp hi).1 d (mem_filter.mp hd).1 j (mem_filter.mp hj).1
      have lim := (mem_filter.mp hd).2
      change M+1-d=z at ev
      dsimp [M] at *
      omega
  have sub : S ∪ (X ∪ Y) ⊆ Ico (a+1) (a+1+2*u) := by
    intro z hz
    rcases mem_union.mp hz with hs|rest
    · obtain ⟨i,hi,j,hj,e,he,eq⟩ := pieces hs
      have il := (mem_filter.mp hi).2.1; have jl := (mem_filter.mp hj).2.1
      have upper_i := (mem_filter.mp hi).2.2; have upper_j := (mem_filter.mp hj).2.2
      dsimp [M] at *
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    rcases mem_union.mp rest with h|h
    · obtain ⟨i,hi,eq⟩ := mem_image.mp h
      have il := pos i (mem_filter.mp hi).1
      have iu := (mem_filter.mp hi).2
      change M+i=z at eq
      dsimp [M] at eq
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨i,hi,eq⟩ := mem_image.mp h
      have il := pos i (mem_filter.mp hi).1
      have iu := (mem_filter.mp hi).2
      change M+1-i=z at eq
      dsimp [M] at eq
      exact mem_Ico.mpr ⟨by omega,by omega⟩
  have card := card_le_card sub
  rw [card_union_of_disjoint free,card_union_of_disjoint xy,cx,cy,Nat.card_Ico] at card
  change S.card+2*R.card ≤ 2*u
  omega


theorem exact_cap {P : Finset ℕ} {D : ℕ} (ne : P.Nonempty) (bounded : Capped P D) :
    ∃ E : ℕ, 0<E ∧ E≤D ∧ Capped P E ∧ Reaches P E := by
  classical
  obtain ⟨z,hz⟩ := ne
  have sing : P.filter (fun x => z ≤ x ∧ x<z+1)={z} := by
    ext x
    simp only [mem_filter,mem_singleton]
    exact ⟨fun ⟨_,lo,hi⟩ => by omega,fun e => ⟨e ▸ hz,by omega,by omega⟩⟩
  have ct : count (tail P z) 1=1 := by rw [tail_count,sing,card_singleton]
  have bd := bounded z 1
  let heights := (range (D+1)).filter (Reaches P)
  have one : 1 ∈ heights := mem_filter.mpr ⟨mem_range.mpr (by omega),z,1,by omega⟩
  let E := heights.max' ⟨1,one⟩
  have top : E ∈ heights := max'_mem _ _
  have ge : 1 ≤ E := le_max' _ 1 one
  have limit := mem_range.mp (mem_filter.mp top).1
  refine ⟨E,ge,by omega,?_,(mem_filter.mp top).2⟩
  intro p n
  have ub := bounded p n
  let h := 2*count (tail P p) n-n
  by_contra! bad
  have rise : Reaches P h := ⟨p,n,by dsimp [h]; omega⟩
  have hl : h ≤ D := by dsimp [h]; omega
  have mem : h ∈ heights := mem_filter.mpr ⟨mem_range.mpr (by omega),rise⟩
  have contr : h ≤ E := le_max' _ h mem
  dsimp [h] at contr
  omega

/-- Any interval of length u captures at most half the positions left
after accounting for the low prefix, up to the global discrepancy D. -/
theorem window_difference_bound {T : Finset ℕ} {p u D : ℕ} (pos : ∀ x ∈ T,0 < x)
    (sep : ∀ i ∈ T,∀ j ∈ T,∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (cap : Capped (T.filter (fun x => p ≤ x ∧ x<p+u)) D) :
    2*(T.filter (fun x => p ≤ x ∧ x<p+u)).card+count T u ≤ u+D := by
  let P := T.filter (fun x => p ≤ x ∧ x<p+u)
  by_cases ne : P.Nonempty
  · obtain ⟨E,hE,le,capE,point⟩ := exact_cap ne cap
    have bounded (x : ℕ) (hx : x ∈ P) : x ≤ u+p := by have e := (mem_filter.mp hx).2.2; omega
    have doub := discrete_sumset hE capE (cap_reverse bounded capE) point (reaches_reverse bounded hE point)
    unfold Bound at doub
    rw [reverse_card bounded] at doub
    have pack := interval_difference_packing (a:=p) (u:=u) pos sep
    rw [Nat.add_comm u p] at pack
    change (sums P (reverse P (p+u))).card+2*count T u ≤ 2*u at pack
    rw [Nat.add_comm p u] at pack
    change 2*P.card+count T u ≤ u+D
    omega
  · have nil : P=∅ := not_nonempty_iff_eq_empty.mp ne
    have sub : T.filter (· < u) ⊆ range u := fun _ hx => mem_range.mpr (mem_filter.mp hx).2
    have ct := card_le_card sub
    rw [card_range] at ct
    change 2*P.card+count T u ≤ u+D
    rw [nil,card_empty]
    change 2*0+(T.filter (· < u)).card ≤ u+D
    omega


end GreenFGY
open GreenFGY Finset

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1_H3_R1.H1 := by
  intro T U D pos sep capped p q pq qU
  let P := T.filter (fun x => p≤x ∧ x<p+(q-p))
  have cap : Capped P D := by
    intro j n
    by_cases outside : U≤j
    · have nil : P.filter (fun x => j≤x ∧ x<j+n)=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨hit,lo,_⟩ := mem_filter.mp hx
        have up := (mem_filter.mp hit).2.2
        omega
      rw [tail_count,nil,card_empty]
      omega
    let k := min n (U-j)
    have inc : P.filter (fun x => j≤x ∧ x<j+n) ⊆ T.filter (fun x => j≤x ∧ x<j+k) := by
      intro x hx
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hx
      obtain ⟨xt,_,up⟩ := mem_filter.mp hit
      exact mem_filter.mpr ⟨xt,lo,by dsimp [k]; omega⟩
    have bd := capped j k (by dsimp [k]; omega)
    have h := card_le_card inc
    have kn : k≤n := min_le_left _ _
    rw [tail_count]
    omega
  have diff := window_difference_bound pos sep cap
  have split := count_split T p (q-p)
  rw [show p+(q-p)=q by omega,tail_count] at split
  change count T q=count T p+P.card at split
  change 2*P.card+count T (q-p) ≤ q-p+D at diff
  change 2*count T q+count T (q-p) ≤ q-p+D+2*count T p
  omega

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H1

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H2

/- Original Lean formalization of Franchi–Gowers–Yip, arXiv:2607.06073.
The integer proofs use half-open windows and the two offsets from adding
unit cells. -/
namespace GreenLocal


open Finset

def window (T : Finset ℕ) (l w : ℕ) := T.filter (fun x => l ≤ x ∧ x < l+w)

def disc (T : Finset ℕ) (l w : ℕ) : ℤ := 2*((window T l w).card:ℤ) - w

theorem card_split (T : Finset ℕ) (l p q : ℕ) :
    (window T l (p+q)).card = (window T l p).card + (window T (l+p) q).card := by
  classical
  have split : window T l (p+q) = window T l p ∪ window T (l+p) q := by
    ext x
    simp only [window,mem_filter,mem_union]
    constructor
    · rintro ⟨h,lo,hi⟩
      by_cases test : x < l+p
      · exact Or.inl ⟨h,lo,test⟩
      · exact Or.inr ⟨h,by omega,by omega⟩
    · rintro (⟨h,lo,hi⟩ | ⟨h,lo,hi⟩) <;> exact ⟨h,by omega,by omega⟩
  have dis : Disjoint (window T l p) (window T (l+p) q) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨_,_,hi⟩ := mem_filter.mp hx
    obtain ⟨_,lo,_⟩ := mem_filter.mp hy
    omega
  rw [split,card_union_of_disjoint dis]

theorem paired (T : Finset ℕ) (h l w : ℕ)
    (noPair : ∀ x ∈ T, x+h ∉ T) :
    (window T l w).card + (window T (l+h) w).card ≤ w := by
  let A := (window T l w).image (·+h)
  let B := window T (l+h) w
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact noPair x (mem_filter.mp hx).1 (mem_filter.mp hb).1
  have sub : A ∪ B ⊆ Ico (l+h) (l+h+w) := by
    intro z hz
    rcases mem_union.mp hz with hA | hB
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hA
      obtain ⟨_,lo,hi⟩ := mem_filter.mp hx
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · exact mem_Ico.mpr (mem_filter.mp hB).2
  have b := card_le_card sub
  rw [card_union_of_disjoint dis,Nat.card_Ico] at b
  have c : A.card = (window T l w).card := card_image_of_injective _ (add_left_injective h)
  rw [c] at b
  dsimp [B] at b
  omega

theorem shorten {T : Finset ℕ} {h l n : ℕ} (pos : 0 < h) (long : h < n)
    (noPair : ∀ x ∈ T, x+h ∉ T) :
    ∃ l' n', l ≤ l' ∧ l'+n' ≤ l+n ∧ n' < n ∧ disc T l n ≤ disc T l' n' := by
  by_cases twice : 2*h ≤ n
  · let rest := n-(h+h)
    have len : n = (h+h)+rest := by dsimp [rest]; omega
    have first := card_split T l h h
    have splits := card_split T l (h+h) rest
    rw [←len] at splits
    have bound := paired T h l h noPair
    refine ⟨l+(h+h),rest,by omega,by omega,by omega,?_⟩
    unfold disc
    omega
  · let w := n-h
    let m := h-w
    have hp : 0 < w := by dsimp [w]; omega
    have hm : w+m = h := by dsimp [w,m]; omega
    have hn : n = h+w := by dsimp [w]; omega
    have left := card_split T l w m
    rw [hm] at left
    have right := card_split T l h w
    rw [←hn] at right
    have bound := paired T h l w noPair
    refine ⟨l+w,m,by omega,by omega,by omega,?_⟩
    unfold disc
    omega

theorem short_subinterval {T : Finset ℕ} {h : ℕ} (pos : 0 < h)
    (noPair : ∀ x ∈ T, x+h ∉ T) (l n : ℕ) :
    ∃ l' n', l ≤ l' ∧ l'+n' ≤ l+n ∧ n' ≤ h ∧ disc T l n ≤ disc T l' n' := by
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases short : n ≤ h
    · exact ⟨l,n,le_rfl,le_rfl,short,le_rfl⟩
    obtain ⟨s,m,low,high,lt,d⟩ := shorten pos (Nat.lt_of_not_ge short) noPair (l := l)
    obtain ⟨r,k,lo,hi,small,enough⟩ := ih m lt s
    exact ⟨r,k,low.trans lo,hi.trans high,small,d.trans enough⟩

theorem disc_split (T : Finset ℕ) (l p q : ℕ) :
    disc T l (p+q) = disc T l p + disc T (l+p) q := by
  simp only [disc,card_split,Nat.cast_add]
  ring

/-- Maximum discrepancy among the half-open integer intervals in [0,U). -/
def Maximizes (T : Finset ℕ) (L w U : ℕ) : Prop :=
  L+w ≤ U ∧ ∀ s n : ℕ, s+n ≤ U → disc T s n ≤ disc T L w

theorem balanced_ends {T : Finset ℕ} {L w U : ℕ} (maximal : Maximizes T L w U)
    (k : ℕ) (kw : k ≤ w) : 0 ≤ disc T L k ∧ 0 ≤ disc T (L+(w-k)) k := by
  obtain ⟨inside,bound⟩ := maximal
  have e1 : k+(w-k)=w := by omega
  have e2 : w-k+k=w := by omega
  have e := disc_split T L k (w-k)
  have f := disc_split T L (w-k) k
  rw [e1] at e
  rw [e2] at f
  have b := bound (L+k) (w-k) (by omega)
  have c := bound L (w-k) (by omega)
  omega

theorem mirror_pair {T : Finset ℕ} {l m n : ℕ}
    (forbid : ∀ x ∈ T, ∀ y ∈ T, x+y+1 ≠ l+m+n) :
    disc T l n + disc T m n ≤ 0 := by
  let f (x : ℕ) := l+m+n-1-x
  let A := (window T l n).image f
  let B := window T m n
  have inj : A.card = (window T l n).card := by
    apply card_image_of_injOn
    intro x hx y hy e
    obtain ⟨_,xl,xu⟩ := mem_filter.mp hx
    obtain ⟨_,yl,yu⟩ := mem_filter.mp hy
    dsimp [f] at e
    omega
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨xt,xl,xu⟩ := mem_filter.mp hx
    have yt := (mem_filter.mp hb).1
    apply forbid x xt _ yt
    dsimp [f]
    omega
  have sub : A ∪ B ⊆ Ico m (m+n) := by
    intro z hz
    rcases mem_union.mp hz with ha | hb
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      obtain ⟨_,xl,xu⟩ := mem_filter.mp hx
      dsimp [f]
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · exact mem_Ico.mpr (mem_filter.mp hb).2
  have card := card_le_card sub
  rw [card_union_of_disjoint dis,inj,Nat.card_Ico] at card
  dsimp [B] at card
  unfold disc
  omega

/-- Discrete version of the left-endpoint condition in FGY Lemma 4.2.
At a point z with L+z in T, no suffix ending at z has positive discrepancy. -/
theorem suffix_nonpositive_of_sum {T : Finset ℕ} {L w U z : ℕ}
    (maximal : Maximizes T L w U) (endBound : z ≤ U) (anchor : L+z ∈ T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (s k : ℕ) (ends : s+k = z) : disc T s k ≤ 0 := by
  have avoid (q n : ℕ) (eq : q+n=z) : disc T L n + disc T q n ≤ 0 := by
    apply mirror_pair
    intro x hx y hy bad
    have h := sep x hx y hy _ anchor
    omega
  by_cases small : k ≤ w
  · have left := (balanced_ends maximal k small).1
    have pair := avoid s k ends
    omega
  · have len : k-w+w=k := by omega
    have split := disc_split T s (k-w) w
    rw [len] at split
    have first := maximal.2 s (k-w) (by omega)
    have last := avoid (s+(k-w)) w (by omega)
    omega

/-- Discrete version of the right-endpoint difference condition in FGY
Lemma 4.2. The argument also works when the difference itself is forbidden
without belonging to T. -/
theorem suffix_nonpositive_of_difference {T : Finset ℕ} {L w U z : ℕ}
    (maximal : Maximizes T L w U) (endBound : z ≤ U) (ordered : z ≤ L+w)
    (absent : ∀ x ∈ T, x+(L+w-z) ∉ T)
    (s k : ℕ) (ends : s+k=z) : disc T s k ≤ 0 := by
  let h := L+w-z
  have pair (q n : ℕ) : disc T q n + disc T (q+h) n ≤ 0 := by
    have b := paired T h q n absent
    unfold disc
    omega
  by_cases small : k ≤ w
  · have eq : s+h = L+(w-k) := by dsimp [h]; omega
    have b := pair s k
    rw [eq] at b
    have right := (balanced_ends maximal k small).2
    omega
  · have len : k-w+w=k := by omega
    have split := disc_split T s (k-w) w
    rw [len] at split
    have first := maximal.2 s (k-w) (by omega)
    have eq : s+(k-w)+h = L := by dsimp [h]; omega
    have last := pair (s+(k-w)) w
    rw [eq] at last
    omega

theorem one_cell (T : Finset ℕ) (s : ℕ) :
    (window T s 1).card = if s ∈ T then 1 else 0 := by
  classical
  by_cases hs : s ∈ T
  · have eq : window T s 1 = {s} := by
      ext x
      simp only [window,mem_filter,mem_singleton]
      constructor
      · rintro ⟨_,l,r⟩; omega
      · rintro rfl; exact ⟨hs,le_rfl,by omega⟩
    simp [eq,hs]
  · have eq : window T s 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨xt,lo,hi⟩ := mem_filter.mp hx
      have e : x=s := by omega
      exact hs (e ▸ xt)
    simp [eq,hs]




open Finset

theorem doubled_with_defect {T A : Finset ℕ} {L U : ℕ}
    (marks : ∀ x, L+x ∈ A → x ≤ U →
      x ∉ T ∧ ∀ t k, t+k=x → disc T t k ≤ 0)
    (s n : ℕ) (inside : s+n ≤ U)
    (H : ℕ) (goodEnd : ∀ t k : ℕ, t+k=s+n → disc T t k ≤ H) :
    2*(window T s n).card + (window A (L+s) n).card ≤ n+H := by
  induction n using Nat.strong_induction_on generalizing s H with
  | h n ih =>
    by_cases empty : window A (L+s) n = ∅
    · have b := goodEnd s n rfl
      unfold disc at b
      rw [empty,card_empty]
      omega
    obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨xt,xl,xr⟩ := mem_filter.mp hx
    let k := x-(L+s)
    let m := n-k-1
    have eq : x = L+(s+k) := by dsimp [k]; omega
    have kn : k< n := by dsimp [k]; omega
    have endEq : k+(1+m)=n := by dsimp [m]; omega
    have hit : L+(s+k) ∈ A := eq ▸ xt
    obtain ⟨miss,reset⟩ := marks (s+k) hit (by omega)
    have first := ih k kn s (by omega) 0 (by simpa using reset)
    have second := ih m (by omega) (s+k+1) (by omega) H
      (fun t len ends => goodEnd t len (by omega))
    have share (P : Finset ℕ) (z : ℕ) :
        (window P z n).card = (window P z k).card + (window P (z+k) 1).card +
          (window P (z+k+1) m).card := by
      have a := card_split P z k (1+m)
      have b := card_split P (z+k) 1 m
      rw [endEq,b] at a
      omega
    have low := share T s
    have high := share A (L+s)
    rw [one_cell,if_neg miss] at low
    have sumEq : L+s+k=L+(s+k) := by omega
    have sumEq' : L+(s+k)+1=L+(s+k+1) := by omega
    rw [one_cell,sumEq,sumEq',if_pos hit] at high
    omega



/-- In the near regime the entire left endpoint of the maximum sits on
the far side of the gap. This uses both occupied endpoints and the
forbidden distance equal to the minimum. -/
theorem near_right {T : Finset ℕ} {a u L w : ℕ} (ha : a ∈ T) (hu : u ∈ T)
    (hL : L ∈ T) (hR : L+w-1 ∈ T) (aL : a ≤ L) (short : w< a) (_wp : 0< w)
    (width : ∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (near : u< L+w+a) : u+a ≤ L+L := by
  by_contra! before
  have rprior : L+w-1+L< u+a := by
    by_contra! after
    have h := width L hL (L+w-1) hR before after
    omega
  have h := width (L+w-1) hR u hu rprior (by omega)
  have avoid := sep (L+w-1) hR a ha u hu
  omega

/-- Last occupied cell strictly before the gap. The four forbidden
sum offsets give two further vacant integer cells beyond a distance a. -/
theorem last_before {T : Finset ℕ} {a u L : ℕ} (ha : a ∈ T) (lu : L< u)
    (width : ∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    ∃ c ∈ T, c+L< u+a ∧
      (∀ t ∈ T, t+L< u+a → t≤ c) ∧ (∀ v ∈ T, c< v → c+a+2< v) := by
  let P := T.filter (fun x => x+L< u+a)
  have ne : P.Nonempty := ⟨a,mem_filter.mpr ⟨ha,by omega⟩⟩
  let c := P.max' ne
  have h := max'_mem P ne
  have hc : c ∈ T ∧ c+L< u+a := mem_filter.mp h
  have greatest (t : ℕ) (ht : t ∈ T) (bef : t+L< u+a) : t≤ c := le_max' P t (mem_filter.mpr ⟨ht,bef⟩)
  refine ⟨c,hc.1,hc.2,greatest,?_⟩
  intro v hv gt
  have side : u+a ≤ v+L := by by_contra! bef; have z := greatest v hv bef; omega
  have dist := width c hc.1 v hv hc.2 side
  have avoid := sep c hc.1 a ha v hv
  omega

theorem boost_reflection {T : Finset ℕ} {L w U a c E : ℕ} (best : Maximizes T L w U)
    (ha : a ∈ T) (amin : ∀ x ∈ T,a ≤ x) (endpoint : L+w-1 ∈ T) (hc : c ∈ T)
    (fits : c+1+w+a ≤ L+w) (gap : ∀x ∈ T,c< x → c+w< x)
    (suffix : ∀ t k : ℕ,t+k=c+1 → disc T t k ≤ E)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    3*(T.filter (· < L+w-a)).card+(window T L w).card ≤ L+w-2*a+E := by
  have ac := amin c hc
  have two : 2*a ≤ L+w := by omega
  let n := L+w-2*a
  let f (x : ℕ) := L+w-1-x
  let P := window T a n
  let A := P.image f
  have apos : 0 < a := by have h := sep a ha a ha a ha; omega
  have len : a+n=L+w-a := by dsimp [n]; omega
  have bound : L+w ≤ U := best.1
  have Pcard : P = T.filter (· < L+w-a) := by
    ext x
    simp only [P,window,mem_filter,len]
    constructor
    · rintro ⟨xt,_,hi⟩; exact ⟨xt,hi⟩
    · rintro ⟨xt,hi⟩; exact ⟨xt,amin x xt,hi⟩
  have cardA : A.card = P.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    obtain ⟨_,xl,xh⟩ := mem_filter.mp hx
    obtain ⟨_,yl,yh⟩ := mem_filter.mp hy
    dsimp [f] at e
    omega
  have allA : window A a n = A := by
    ext x
    simp only [window,mem_filter,and_iff_left_iff_imp]
    intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨_,yl,yh⟩ := mem_filter.mp hy
    dsimp [f]
    exact ⟨by omega,by omega⟩
  have forbidden (h : ℕ) (hm : h ∈ T) (d : ℕ) (diff : h ≤ d ∧ d ≤ h+1) :
      ∀x∈T, x+d ∉ T := by
    intro x hx hit
    have b := sep x hx h hm (x+d) hit
    omega
  have last : ∀ t k, t+k=a+n → disc T t k ≤ 0 := by
    intro t k e
    apply suffix_nonpositive_of_difference best (by omega) (by omega) _ t k e
    apply forbidden a ha
    omega

  have marks (x : ℕ) (mark : 0+x ∈ A) (hU : x ≤ U) :
      x ∉ T ∧ ∀ t k,t+k=x → disc T t k ≤ 0 := by
    rw [Nat.zero_add] at mark
    obtain ⟨y,hy,ex⟩ := mem_image.mp mark
    obtain ⟨yt,yl,yh⟩ := mem_filter.mp hy
    dsimp [f] at ex
    refine ⟨?_,suffix_nonpositive_of_difference best hU (by omega) (forbidden y yt _ (by omega))⟩
    intro xt
    have e := sep x xt y yt (L+w-1) endpoint
    omega
  let k := c+1-a
  let r := n-k-w
  have kdef : a+k=c+1 := by dsimp [k]; omega
  have rdef : k+(w+r)=n := by dsimp [r]; omega
  have taildef : (a+k+w)+r=a+n := by omega
  have lower := doubled_with_defect marks a k (by omega) E (fun t z hit => suffix t z (by omega))
  have upper := doubled_with_defect marks (a+k+w) r (by omega) 0
    (fun t z hit => last t z (by omega))
  simp only [Nat.zero_add,Nat.add_zero] at lower upper
  have mid : window T (a+k) w=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hit,lo,hi⟩ := mem_filter.mp hx
    have g := gap x hit (by omega)
    omega
  let F := window T L w
  let Z := F.image (fun i => L+w+c-i)
  have cz : Z.card=F.card := by
    apply card_image_of_injOn
    intro i hi j hj e
    have ui := (mem_filter.mp hi).2.2; have uj := (mem_filter.mp hj).2.2
    change L+w+c-i=L+w+c-j at e
    omega
  have avoid : Disjoint Z (window A (a+k) w) := by
    apply disjoint_left.mpr
    intro x hx hz
    obtain ⟨i,hi,eq⟩ := mem_image.mp hx
    obtain ⟨it,il,iu⟩ := mem_filter.mp hi
    obtain ⟨z,hz,e⟩ := mem_image.mp (mem_filter.mp hz).1
    obtain ⟨zt,zl,zu⟩ := mem_filter.mp hz
    change L+w+c-i=x at eq
    dsimp [f] at e
    have bad := sep z zt c hc i it
    omega
  have sub : Z ∪ window A (a+k) w ⊆ Ico (a+k) (a+k+w) := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · obtain ⟨i,hi,e⟩ := mem_image.mp h
      obtain ⟨_,il,iu⟩ := mem_filter.mp hi
      change L+w+c-i=x at e
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · exact mem_Ico.mpr (mem_filter.mp h).2
  have central := card_le_card sub
  rw [card_union_of_disjoint avoid,cz,Nat.card_Ico] at central
  have split (S : Finset ℕ) :
      (window S a n).card = (window S a k).card + (window S (a+k) w).card +
        (window S (a+k+w) r).card := by
    have l := card_split S a k (w+r)
    have h := card_split S (a+k) w r
    rw [rdef,h] at l
    omega
  have low := split T
  have high := split A
  rw [mid,card_empty] at low
  rw [allA,cardA] at high
  change P.card = _ at low
  change 3*(T.filter (· < L+w-a)).card+F.card ≤ n+E
  rw [←Pcard]
  omega



open Finset
open scoped Pointwise

def F (T : Finset ℕ) (j : ℕ) := (T.filter (· < j)).card

theorem prefix_partition (T : Finset ℕ) {p q : ℕ} (ord : p ≤ q) :
    F T q = F T p+(window T p (q-p)).card := by
  have split := card_split T 0 p (q-p)
  have pref (j : ℕ) : window T 0 j=T.filter (· < j) := by
    ext x
    simp [window]
  rw [show p+(q-p)=q by omega,pref,pref,Nat.zero_add] at split
  exact split

theorem partition_len (T : Finset ℕ) (p n : ℕ) :
    F T (p+n)=F T p+(window T p n).card := by
  have s := prefix_partition T (Nat.le_add_right p n)
  rwa [Nat.add_sub_cancel_left] at s

theorem le_prefix (T : Finset ℕ) {p q : ℕ} (ord : p ≤ q) : F T p ≤ F T q :=
  card_le_card (fun _ hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.trans_le ord⟩)

theorem sparse_end {T : Finset ℕ} {c E : ℕ} (h : F T c ≤ E) (s k : ℕ) (eq : s+k=c) :
    disc T s k ≤ E := by
  have all : window T s k ⊆ T.filter (· < c) := by
    intro x hx
    obtain ⟨hit,_,hi⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hit,by omega⟩
  have lim : window T s k ⊆ Ico s (s+k) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
  have ln : (window T s k).card ≤ k := by simpa using card_le_card lim
  have small : (window T s k).card ≤ F T c := card_le_card all
  unfold disc
  omega

/-- Disjointness of the terminal part and a thickened sum. Including the
rightmost occupied cell of the maximizing interval gives a strict saving. -/
theorem near_sum {T : Finset ℕ} {a u L w : ℕ} (ha : a ∈ T) (hU : u+2*a ∈ T)
    (amin : ∀x ∈ T,a ≤ x) (endpoint : L+w-1 ∈ T) (start : L< u) (short : w< a)
    (wp : 0< w) (inside : L+w< u+a)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    F T (u+2*a)+F T (u+a-L)+F T (L+a)+1 ≤
      F T (L+w+a)+F T (L+w)+(u+a-(L+w)) := by
  let b := L+w
  let r := u+a-L
  let A := T.filter (· < r)
  let B := insert (b-1) (window T b (L+a-b))
  let K : Finset ℕ := {1,2}
  let S := (A+B)+K
  let J := window T (b+a) (u+2*a-(b+a))
  have hA : A.Nonempty := ⟨a,mem_filter.mpr ⟨ha,by dsimp [r]; omega⟩⟩
  have hB : B.Nonempty := ⟨_,mem_insert_self _ _⟩
  have cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hB
  have cd' := cauchy_davenport_add_of_linearOrder_isCancelAdd (hA.add hB)
    (show K.Nonempty from ⟨1,by simp [K]⟩)
  have ck : K.card=2 := by decide
  have bound (z : ℕ) (hz : z ∈ S) : b+a ≤ z ∧ z < u+2*a ∧ z ∉ T := by
    obtain ⟨s,hs,e,he,eq⟩ := mem_add.mp hz
    obtain ⟨i,hi,j,hj,et⟩ := mem_add.mp hs
    have il := amin i (mem_filter.mp hi).1
    have ir := (mem_filter.mp hi).2
    have lowJ : b ≤ L+a := by dsimp [b]; omega
    have jj : j ∈ T ∧ b-1 ≤ j ∧ j < L+a := by
      rcases mem_insert.mp hj with rfl|h
      · exact ⟨endpoint,le_rfl,by dsimp [b]; omega⟩
      · obtain ⟨jt,jlo,jhi⟩ := mem_filter.mp h
        exact ⟨jt,by omega,by omega⟩
    have ee : e=1 ∨ e=2 := by simpa [K] using he
    have blocked : z ∉ T := by
      intro hit
      have bad := sep i (mem_filter.mp hi).1 j jj.1 z hit
      omega
    have last : z≠u+2*a := fun e => blocked (e ▸ hU)
    dsimp [r] at ir
    dsimp [b] at *
    exact ⟨by omega,by omega,blocked⟩
  have dis : Disjoint S J := by
    apply disjoint_left.mpr
    intro z hs hj
    exact (bound z hs).2.2 (mem_filter.mp hj).1
  have sub : S ∪ J ⊆ Ico (b+a) (u+2*a) := by
    intro z hz
    rcases mem_union.mp hz with hs|hj
    · exact mem_Ico.mpr ⟨(bound z hs).1,(bound z hs).2.1⟩
    · obtain ⟨_,lo,hi⟩ := mem_filter.mp hj
      dsimp [b] at *
      exact mem_Ico.mpr ⟨lo,by omega⟩
  have space := card_le_card sub
  rw [card_union_of_disjoint dis,Nat.card_Ico] at space
  have splitB := prefix_partition T (show b≤ L+a by dsimp [b]; omega)
  have splitJ := prefix_partition T (show b+a≤ u+2*a by dsimp [b]; omega)
  have miss : b-1 ∉ window T b (L+a-b) := by
    intro hit
    have lo := (mem_filter.mp hit).2.1
    dsimp [b] at lo
    omega
  have cardB : B.card=(window T b (L+a-b)).card+1 := card_insert_of_notMem miss
  change S.card ≥ _ at cd'
  change F T (u+2*a) = F T (b+a)+J.card at splitJ
  change F T (u+2*a)+A.card+F T (L+a)+1 ≤ F T (b+a)+F T b+(u+a-b)
  dsimp [b] at *
  omega

theorem ends_before_lower {T : Finset ℕ} {a u L w : ℕ} (best : Maximizes T L w (u+2*a))
    (ha : a ∈ T) (hu : u ∈ T) (hU : u+2*a ∈ T)
    (amin : ∀x ∈ T,a ≤ x) (start : L< u) (inside : L+w< u+a)
    (left : L ∈ T) (right : L+w-1 ∈ T) (short : w< a) (wp : 0< w)
    (width : ∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (failed : u+a ≤ F T u+F T (u+a)+F T (u+2*a)) : L+w+1 < u := by
  by_contra! near
  let b := L+w
  let d := b-a
  let r := u+a-L
  let E := F T r
  have aL := amin L left
  have apos : 0< a := by omega
  have across := near_right ha hu left right aL short wp width sep (by omega)
  obtain ⟨c,hc,low,_,empty⟩ := last_before ha start width sep
  have cL : c< L := by omega
  have lim := empty L left cL
  have cmin := amin c hc
  have largeL : 2*a ≤ L := by omega
  have cr : c+1 ≤ r := by dsimp [r]; omega
  have suffix := sparse_end (le_prefix T cr)
  have gain := boost_reflection (E:=E) best ha amin right hc (by omega)
    (fun x hx gt => by have h := empty x hx gt; omega) suffix sep
  change 3*F T d+(window T L w).card ≤ L+w-2*a+E at gain
  have disc (p q : ℕ) (pq : p≤ q) (hi : q≤ u+2*a) :
      2*F T q-2*F T p+w ≤ q-p+2*(window T L w).card := by
    have pack := best.2 p (q-p) (by omega)
    have part := prefix_partition T pq
    unfold GreenLocal.disc at pack
    omega
  have bdef : b=L+w := rfl
  have ddef : d=b-a := rfl
  have du : d≤ u := by omega
  have lowI := disc d u du (by omega)
  have first := disc d b (by omega) (by omega)
  have last := disc L (L+a) (by omega) (by omega)
  have pop := partition_len T L w
  change F T b=F T L+(window T L w).card at pop
  have paired := paired T a L w (fun x hx hit => by have h := sep x hx a ha (x+a) hit; omega)
  have p := partition_len T (L+a) w
  rw [show L+a+w=b+a by omega] at p
  have sum := near_sum ha hU amin right start short wp inside sep
  have middle : F T (u+a) ≤ F T (b+a) := by
    by_cases ord : u+a ≤ b+a
    · exact le_prefix T ord
    have eq : b+a+1=u+a := by omega
    have nil : window T (b+a) 1=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hx
      have bad := sep u hu a ha x hit
      omega
    have k := partition_len T (b+a) 1
    rw [eq,nil,card_empty,add_zero] at k
    omega
  change F T (u+2*a)+F T r+F T (L+a)+1 ≤ F T (b+a)+F T b+(u+a-b) at sum
  have er : E=F T r := rfl
  have step1 : 2*F T u+4*F T d+3*a ≤ u+L+2*F T r := by omega
  have side1 : 2*F T L+w ≤ 2*F T d+a := by omega
  have side2 : 2*F T (L+a)+w ≤ 2*F T b+a := by omega
  have pairSize : F T b+F T (b+a) ≤ w+F T L+F T (L+a) := by omega
  omega


class DifferenceBounds (T : Finset ℕ) (U D : ℕ) : Prop where
  bound : ∀ p q : ℕ, p≤ q → q≤ U → 2*F T q+F T (q-p) ≤ q-p+D+2*F T p

theorem interval_difference {T : Finset ℕ} {L w U D : ℕ} [bounds : DifferenceBounds T U D]
    (_best : Maximizes T L w U) (_eq : w+D=2*(window T L w).card) (_pos : ∀ x∈T,0< x)
    (_sep : ∀ i∈T,∀ j∈T,∀ l∈T,l+1 < i+j ∨ i+j+2 < l)
    (p q : ℕ) (pq : p≤ q) (qu : q≤ U) : 2*F T q+F T (q-p) ≤ q-p+D+2*F T p :=
  bounds.bound p q pq qu

theorem discrepancy_prefix {T : Finset ℕ} {L w U D : ℕ} (best : Maximizes T L w U)
    (discEq : w+D=2*(window T L w).card)
    (p q : ℕ) (pq : p≤ q) (qu : q≤ U) : 2*F T q ≤ 2*F T p+(q-p)+D := by
  have h := best.2 p (q-p) (by omega)
  have k := prefix_partition T pq
  unfold disc at h
  omega

theorem reflected_disjoint_count {T P : Finset ℕ} {M l r : ℕ} (lr : l ≤ r)
    (ord : ∀ i ∈ P,i ≤ M)
    (support : ∀ i ∈ P,l ≤ M-i ∧ M-i< r ∧ M-i ∉ T) :
    P.card+F T r ≤ r-l+F T l := by
  let X := P.image (M-·)
  let R := window T l (r-l)
  have inj : X.card=P.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    have o := ord x hx; have o' := ord y hy
    change M-x=M-y at e
    omega
  have free : Disjoint X R := by
    apply disjoint_left.mpr
    intro z hx hr
    obtain ⟨i,hi,e⟩ := mem_image.mp hx
    exact (support i hi).2.2 (e ▸ (mem_filter.mp hr).1)
  have inc : X ∪ R ⊆ Ico l r := by
    intro z hz
    rcases mem_union.mp hz with hx|hr
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact mem_Ico.mpr ⟨(support i hi).1,(support i hi).2.1⟩
    · obtain ⟨_,lo,hi⟩ := mem_filter.mp hr
      exact mem_Ico.mpr ⟨lo,by omega⟩
  have room := card_le_card inc
  rw [card_union_of_disjoint free,inj,Nat.card_Ico] at room
  have part := prefix_partition T lr
  change F T r=F T l+R.card at part
  omega

theorem bridge {T : Finset ℕ} {a u L w : ℕ}
    (high : u+2*a ∈ T) (lu : L< u) (wp : 0< w)
    (gap : ∀t ∈ T,t+L< u+a ∨ u+2*a< t+L+w)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    F T (u+2*a-L)+(window T L w).card ≤ F T (u+a-L)+w := by
  let y := u+2*a-L
  let r := u+a-L
  let B := window T r (y-r)
  have ry : r≤ y := by dsimp [r,y]; omega
  have bd : ∀i ∈ B,i≤ u+2*a-1 := by
    intro i hi
    have lim := (mem_filter.mp hi).2.2
    dsimp [y,r] at *
    omega
  have holes := reflected_disjoint_count (T:=T) (P:=B) (M:=u+2*a-1) (l:=L) (r:=L+w)
    (by omega) bd (by
      intro i hi
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hi
      have jump := gap i hit
      dsimp [y,r] at *
      refine ⟨by omega,by omega,?_⟩
      intro bad
      have h := sep i hit (u+2*a-1-i) bad (u+2*a) high
      omega)
  have part := prefix_partition T ry
  have wp := partition_len T L w
  change F T y=F T r+B.card at part
  change F T y+(window T L w).card ≤ F T r+w
  omega



open Finset
open scoped Pointwise

theorem prefix_ends_empty {T : Finset ℕ} {a : ℕ} (amin : ∀ i ∈ T,a ≤ i) : F T a=0 := by
  have nil : T.filter (· < a)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_lt_of_ge (amin x (mem_filter.mp hx).1)) (mem_filter.mp hx).2
  simp [F,nil]

theorem terminal_sum {T : Finset ℕ} {a u L : ℕ} (ha : a ∈ T) (hu : u ∈ T) (hU : u+2*a ∈ T)
    (amin : ∀x ∈ T,a ≤ x) (lu : L< u) (short : u≤ L+a)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) :
    F T (u+2*a)+F T (u+a-L)+F T (L+a)+1 ≤ a+F T (u+a)+F T u := by
  let r := u+a-L
  let A := T.filter (· < r)
  let B := window T u (L+a+1-u)
  let S := (A+B)+range 3
  let J := window T (u+a) a
  have hA : A.Nonempty := ⟨a,mem_filter.mpr ⟨ha,by dsimp [r]; omega⟩⟩
  have hB : B.Nonempty := ⟨u,mem_filter.mpr ⟨hu,by omega,by omega⟩⟩
  have cd := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hB
  have cd' := cauchy_davenport_add_of_linearOrder_isCancelAdd (hA.add hB)
    (show (range 3).Nonempty from ⟨0,by decide⟩)
  change (A+B).card+(range 3).card-1 ≤ S.card at cd'
  rw [card_range] at cd'
  have bound (z : ℕ) (hz : z ∈ S) : u+a≤ z ∧ z< u+2*a ∧ z∉T := by
    obtain ⟨t,ht,k,hk,e⟩ := mem_add.mp hz
    obtain ⟨i,hi,j,hj,eq⟩ := mem_add.mp ht
    obtain ⟨jt,jl,jr⟩ := mem_filter.mp hj
    have it := (mem_filter.mp hi).1
    have il := amin i it
    have ir := (mem_filter.mp hi).2
    have kl := mem_range.mp hk
    have last := sep i it j jt (u+2*a) hU
    dsimp [r] at ir
    refine ⟨by omega,by omega,?_⟩
    intro bad
    have h := sep i it j jt z bad
    omega
  have dis : Disjoint S J := by
    apply disjoint_left.mpr
    intro z hs hj
    exact (bound z hs).2.2 (mem_filter.mp hj).1
  have sub : S ∪ J ⊆ Ico (u+a) (u+2*a) := by
    intro z hz
    rcases mem_union.mp hz with hs|hj
    · exact mem_Ico.mpr ⟨(bound z hs).1,(bound z hs).2.1⟩
    · obtain ⟨_,lo,hi⟩ := mem_filter.mp hj
      exact mem_Ico.mpr ⟨lo,by omega⟩
  have room := card_le_card sub
  rw [card_union_of_disjoint dis,Nat.card_Ico] at room
  have pop := partition_len T (u+a) a
  rw [show u+a+a=u+2*a by omega] at pop
  change F T (u+2*a)=F T (u+a)+J.card at pop
  have split := prefix_partition T (show u≤ L+a+1 by omega)
  change F T (L+a+1)=F T u+B.card at split
  have mon := le_prefix T (show L+a≤ L+a+1 by omega)
  change F T (u+2*a)+A.card+F T (L+a)+1 ≤ a+F T (u+a)+F T u
  omega



open Finset
open scoped Pointwise

theorem MarkBranch {T : Finset ℕ} {a u L w D : ℕ} [DifferenceBounds T (u+2*a) D] (best : Maximizes T L w (u+2*a))
    (ha : a ∈ T) (hu : u ∈ T) (hU : u+2*a ∈ T)
    (amin : ∀x ∈ T,a ≤ x) (start : L< u) (inside : L+w< u+a)
    (left : L ∈ T) (right : L+w-1 ∈ T) (short : w< a) (wp : 0< w)
    (de : w+D=2*(window T L w).card)
    (mass : F T u+2*F T (u+a) ≤ u+D)
    (gap : ∀t ∈ T,t+L< u+a ∨ u+2*a< t+L+w)
    (width : ∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (failed : u+a ≤ F T u+F T (u+a)+F T (u+2*a)) (close : u≤ L+a) (mark : (∃ z ∈ T,L+w+a≤ z ∧ z< u+a)) : False := by
  let b := L+w
  let y := u+2*a-L
  let r := u+a-L
  have bl : b=L+w := rfl
  have yl : y+L=u+2*a := by dsimp [y]; omega
  have rl : r+L=u+a := by dsimp [r]; omega
  have near := ends_before_lower best ha hu hU amin start inside left right short wp width sep failed
  have pop := partition_len T L w
  change F T b=F T L+(window T L w).card at pop
  have size : (window T L w).card ≤ w := by
    have sb : window T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card sb
  have aL := amin L left
  obtain ⟨z,hz,zl,zr⟩ := mark
  have small := reflected_disjoint_count (P:=window T L w) (M:=z) (l:=a) (r:=r)
    (by omega) (by
      intro i hi
      have upper := (mem_filter.mp hi).2.2
      omega) (by
        intro i hi
        obtain ⟨it,il,iu⟩ := mem_filter.mp hi
        refine ⟨by omega,by omega,?_⟩
        intro hit
        have h := sep i it (z-i) hit z hz
        omega)
  rw [prefix_ends_empty amin] at small
  have jump := bridge hU start wp gap sep
  change F T y+(window T L w).card ≤ F T r+w at jump
  have diff := interval_difference best de (fun x hx => by have h := amin x hx; omega)
    sep y (u+2*a) (by omega) le_rfl
  rw [show u+2*a-y=L by omega] at diff
  have zd := discrepancy_prefix best de L u (by omega) (by omega)
  clear * - small jump diff zd de size failed mass yl rl bl near close short wp start aL
  omega


open Finset
open scoped Pointwise

theorem EmptyBranch {T : Finset ℕ} {a u L w D : ℕ} (best : Maximizes T L w (u+2*a))
    (ha : a ∈ T) (hu : u ∈ T) (hU : u+2*a ∈ T)
    (amin : ∀x ∈ T,a ≤ x) (start : L< u) (inside : L+w< u+a)
    (left : L ∈ T) (right : L+w-1 ∈ T) (short : w< a) (wp : 0< w)
    (de : w+D=2*(window T L w).card)
    (_mass : F T u+2*F T (u+a) ≤ u+D)
    (_gap : ∀t ∈ T,t+L< u+a ∨ u+2*a< t+L+w)
    (width : ∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (failed : u+a ≤ F T u+F T (u+a)+F T (u+2*a)) (close : u≤ L+a) (mark : ¬ (∃ z ∈ T,L+w+a≤ z ∧ z< u+a)) : False := by
  let b := L+w
  let y := u+2*a-L
  let r := u+a-L
  have bl : b=L+w := rfl
  have yl : y+L=u+2*a := by dsimp [y]; omega
  have rl : r+L=u+a := by dsimp [r]; omega
  have near := ends_before_lower best ha hu hU amin start inside left right short wp width sep failed
  have pop := partition_len T L w
  change F T b=F T L+(window T L w).card at pop
  have size : (window T L w).card ≤ w := by
    have sb : window T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card sb
  have aL := amin L left
  let d := b-a
  let E := F T r
  have dval : d=b-a := rfl
  have front := near_right ha hu left right aL short wp width sep (by omega)
  obtain ⟨c,hc,lc,_,empty⟩ := last_before ha start width sep
  have cL : c< L := by omega
  have lim := empty L left cL
  have cm := amin c hc
  have gain := boost_reflection (E:=E) best ha amin right hc (by omega)
    (fun x hx gt => by have h := empty x hx gt; omega)
    (sparse_end (le_prefix T (show c+1≤ r by omega))) sep
  change 3*F T d+(window T L w).card ≤ b-2*a+E at gain
  have er : E=F T r := rfl
  have du := discrepancy_prefix best de d u (by omega) (by omega)
  have db := discrepancy_prefix best de d b (by omega) (by omega)
  have Lm := discrepancy_prefix best de L (L+a) (by omega) (by omega)
  have Lu := discrepancy_prefix best de L u start.le (by omega)
  have paire := paired T a L w (fun x hx hit => by have h := sep x hx a ha (x+a) hit; omega)
  have p := partition_len T (L+a) w
  rw [show L+a+w=b+a by omega] at p
  have equalF : F T (u+a)=F T (b+a) := by
    have nil : window T (b+a) (u+a-(b+a))=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hx
      exact mark ⟨x,hit,lo,by omega⟩
    have h := prefix_partition T (show b+a≤ u+a by omega)
    rwa [nil,card_empty,add_zero] at h
  have term := terminal_sum ha hu hU amin start close sep
  change F T (u+2*a)+F T r+F T (L+a)+1 ≤ a+F T (u+a)+F T u at term
  have bigL : 2*a≤ L := by
    clear * - cm lim
    omega
  have sumD : d+a=b := Nat.sub_add_cancel (aL.trans (Nat.le_add_right L w))
  have dU : d≤ u := (Nat.sub_le b a).trans (by clear * - near bl; omega)
  have gain' : 3*F T d+(window T L w).card+2*a ≤ b+E := by
    clear * - gain bl bigL
    omega
  have du' : 2*F T u+d ≤ 2*F T d+u+D := by
    clear * - du dU
    omega
  have step1 : 2*F T u+4*F T d+3*a ≤ u+L+2*F T r := by linarith only [gain', du', bl, sumD, de, er]
  have side1 : 2*F T L+w ≤ 2*F T d+a := by
    clear * - db sumD pop de
    omega
  have side2 : 2*F T (L+a)+w ≤ 2*F T b+a := by
    clear * - Lm pop de
    omega
  have side3 : 2*F T u+w+L ≤ 2*F T b+u := by
    clear * - Lu start pop de
    omega
  have pairSize : F T b+F T (b+a) ≤ w+F T L+F T (L+a) := by
    clear * - p paire pop
    omega
  linarith only [step1,side1,side2,side3,pairSize,term,equalF,failed]



open Finset

theorem far_left {T : Finset ℕ} {a u L w D : ℕ} [DifferenceBounds T (u+2*a) D] (best : Maximizes T L w (u+2*a))
    (ha : a ∈ T) (hu : u ∈ T) (hU : u+2*a ∈ T)
    (amin : ∀x ∈ T,a ≤ x) (start : L< u) (inside : L+w< u+a)
    (left : L ∈ T) (right : L+w-1 ∈ T) (short : w< a) (wp : 0< w)
    (de : w+D=2*(window T L w).card)
    (mass : F T u+2*F T (u+a) ≤ u+D)
    (gap : ∀t ∈ T,t+L< u+a ∨ u+2*a< t+L+w)
    (width : ∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (failed : u+a ≤ F T u+F T (u+a)+F T (u+2*a)) : L+a< u := by
  by_contra! near
  by_cases mark : ∃ z ∈ T,L+w+a≤ z ∧ z< u+a
  · exact MarkBranch best ha hu hU amin start inside left right short wp de mass gap width sep failed near mark
  · exact EmptyBranch best ha hu hU amin start inside left right short wp de mass gap width sep failed near mark



open Finset

private theorem prefix_start_empty {T : Finset ℕ} {a : ℕ} (amin : ∀ i ∈ T,a ≤ i) : F T a=0 := by
  have nil : T.filter (· < a)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_lt_of_ge (amin x (mem_filter.mp hx).1)) (mem_filter.mp hx).2
  simp [F,nil]


/-- At an occupied sum with the left endpoint of the maximum, each
input below the tested point consumes two positions. -/
theorem anchored_window {T : Finset ℕ} {L w U : ℕ} (best : Maximizes T L w U)
    (hL : L ∈ T) (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    {p q : ℕ} (pq : p≤ q) (qu : q≤ U) (hit : L+q ∈ T) :
    2*F T q+F T (L+q) ≤ q-p+2*F T p+F T (L+p) := by
  have marks (x : ℕ) (h : L+x ∈ T) (xu : x≤ U) :
      x∉T ∧ ∀ j n,j+n=x → disc T j n ≤ 0 := by
    refine ⟨?_,suffix_nonpositive_of_sum best xu h sep⟩
    intro xt
    have bad := sep L hL x xt (L+x) h
    omega
  have h := doubled_with_defect marks p (q-p) (by omega) 0
    (fun j n eq => suffix_nonpositive_of_sum best qu hit sep j n (by omega))
  have p1 := prefix_partition T pq
  have p2 := partition_len T (L+p) (q-p)
  rw [show L+p+(q-p)=L+q by omega] at p2
  omega

theorem surplus {T : Finset ℕ} {a u L w D : ℕ} [DifferenceBounds T (u+2*a) D] (best : Maximizes T L w (u+2*a))
    (hu : u ∈ T) (amin : ∀ x ∈ T,a ≤ x) (pos : 0< a)
    (hL : L ∈ T) (large : 2*a< L) (far : L+a< u)
    (de : w+D=2*(window T L w).card) (mass : F T u+2*F T (u+a)≤ u+D)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (failed : u+a≤ F T u+F T (u+a)+F T (u+2*a)) :
    let y := u+2*a-L
    let k := u-L
    ∃ g : ℕ,2*F T k+F T u+g=k-a+F T (L+a) ∧
      5*a+2*g+4*F T k ≤ 5*D+4*F T y := by
  let y := u+2*a-L
  let k := u-L
  have ey : y+L=u+2*a := by dsimp [y]; omega
  have ek : L+k=u := by dsimp [k]; omega
  have aK : a≤ k := by omega
  have mark := anchored_window best hL sep aK (by omega) (ek ▸ hu)
  rw [ek,prefix_start_empty amin] at mark
  have diff := interval_difference best de (fun i hi => pos.trans_le (amin i hi))
    sep y (u+2*a) (by omega) le_rfl
  rw [show u+2*a-y=L by omega] at diff
  have d := discrepancy_prefix best de L (L+a) (by omega) (by omega)
  let g := k-a+F T (L+a)-(2*F T k+F T u)
  have eg : 2*F T k+F T u+g=k-a+F T (L+a) := by dsimp [g]; omega
  change ∃ g,2*F T k+F T u+g=k-a+F T (L+a) ∧ 5*a+2*g+4*F T k ≤ 5*D+4*F T y
  exact ⟨g,eg,by omega⟩

theorem no_middle_mark {T : Finset ℕ} {a u L w D c : ℕ}
    (_lb : 2*a< L) (far : L+a< u) (short : w< a) (wp : 0< w) (ha : a ∈ T) (hu : u ∈ T) (hU : u+2*a ∈ T)
    (de : w+D=2*(window T L w).card)
    (gap : ∀t ∈ T,t+L< u+a ∨ u+2*a< t+L+w)
    (low : c+L< u+a) (greatest : ∀t ∈ T,t+L< u+a → t≤ c)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (sur : a+F T (u-L) < D+F T (u+2*a-L)) :
    ∀ z ∈ T,z≤ u+a → z+a< c+(L+w) := by
  intro z hz hi
  by_contra! loc
  let k := u-L
  let r := u+a-L
  let y := u+2*a-L
  let b := L+w
  let l := min k (z-(b-1))
  let P := window T L w
  let Q := window T k (r-k)
  have ey : y+L=u+2*a := by dsimp [y]; omega
  have ek : k+L=u := by dsimp [k]; omega
  have er : r+L=u+a := by dsimp [r]; omega
  have be : b=L+w := rfl
  have jump := bridge hU (by omega : L< u) wp gap sep
  change F T y+P.card ≤ F T r+w at jump
  have rg : k≤ r := by omega
  have qt := prefix_partition T rg
  change F T r=F T k+Q.card at qt
  have cK : k≤ c := by
    by_contra! below
    have nil : Q=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hit,lo,hi⟩ := mem_filter.mp hx
      have h := greatest x hit (by omega)
      omega
    rw [nil,card_empty] at qt
    have bound : P.card ≤ w := by
      have sub : P ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
      simpa using card_le_card sub
    change w+D=2*P.card at de
    change a+F T k < D+F T y at sur
    omega
  have zmid : z< u+a := by
    by_contra! high
    have eq : z=u+a := by omega
    have bad := sep u hu a ha z hz
    omega
  have zb : b-1 ≤ z := by omega
  let X := P.image (z-·)
  have free : Disjoint X Q := by
    apply disjoint_left.mpr
    intro x hx hq
    obtain ⟨i,hi,e⟩ := mem_image.mp hx
    obtain ⟨it,il,iu⟩ := mem_filter.mp hi
    change z-i=x at e
    have bad := sep i it x (mem_filter.mp hq).1 z hz
    omega
  have cx : X.card=P.card := by
    apply card_image_of_injOn
    intro i hi j hj e
    have iu := (mem_filter.mp hi).2.2; have ju := (mem_filter.mp hj).2.2
    change z-i=z-j at e
    omega
  have sub : X ∪ Q ⊆ Ico l (l+a) := by
    intro x hx
    rcases mem_union.mp hx with hx|hq
    · obtain ⟨i,hi,e⟩ := mem_image.mp hx
      obtain ⟨_,il,iu⟩ := mem_filter.mp hi
      change z-i=x at e
      dsimp [l]
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨hit,lo,up⟩ := mem_filter.mp hq
      have xc := greatest x hit (by omega)
      dsimp [l]
      exact mem_Ico.mpr ⟨by omega,by omega⟩
  have room := card_le_card sub
  rw [card_union_of_disjoint free,cx,Nat.card_Ico] at room
  change w+D=2*P.card at de
  change a+F T k < D+F T y at sur
  omega

/-- Occupied cells on opposite sides of the middle prefix are separated
by at least one minimum. The two reflected pieces use disjoint parts of
a single copy of the holes in the maximizing interval. -/
theorem central_width {T : Finset ℕ} {a u L w D c : ℕ}
    (far : L+a< u) (short : w< a) (wp : 0< w) (hU : u+2*a ∈ T)
    (de : w+D=2*(window T L w).card)
    (gap : ∀t ∈ T,t+L< u+a ∨ u+2*a< t+L+w)
    (low : c+L< u+a) (greatest : ∀t ∈ T,t+L< u+a → t≤ c)
    (empty : ∀v ∈ T,c< v → c+a+2< v)
    (prior : ∀z ∈ T,z≤ u+a → z+a< c+(L+w))
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (sur : a+F T (u-L)< D+F T (u+2*a-L)) :
    ∀ z ∈ T, ∀ v ∈ T,z< u+a → u+a≤ v → z+a≤ v := by
  intro z hz v hv zl vh
  by_contra! narrow
  let s := u+2*a
  let r := u+a-L
  let k := u-L
  let y := s-L
  let b := L+w
  have es : s=u+2*a := rfl
  have er : r+L=u+a := by dsimp [r]; omega
  have ek : k+L=u := by dsimp [k]; omega
  have ey : y+L=s := by dsimp [s,y]; omega
  have eb : b=L+w := rfl
  have zp := prior z hz zl.le
  let P := window T L w
  let H := Finset.Ico L b \ P
  let Hhi := H.filter (v-c ≤ ·)
  let Hlo := H.filter (· < v-c)
  let Q := window T k (r-k)
  let R := window T r (y-r)
  let J := Ico (z-L+1) (v-(b-1))
  let X := H.image (z-·)
  let Y := Hhi.image (v-·)
  let Z := Hlo.image (s-1-·)
  have pi : P ⊆ Ico L b := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
  have ch : H.card=w-P.card := by dsimp [H]; rw [card_sdiff_of_subset pi,Nat.card_Ico]; omega
  have pc : P.card ≤ w := by have h := card_le_card pi; rw [Nat.card_Ico] at h; omega
  have partition : Hlo.card+Hhi.card=H.card := by
    simpa only [Hlo,Hhi,not_lt] using card_filter_add_card_filter_not (s:=H) (fun i => i< v-c)
  have inc : Q ⊆ (X ∪ Y) ∪ J := by
    intro x hx
    obtain ⟨hit,xl,xu⟩ := mem_filter.mp hx
    have xc := greatest x hit (by omega)
    by_cases side : x≤ z-L
    · apply mem_union_left
      apply mem_union_left
      apply mem_image.mpr
      refine ⟨z-x,mem_sdiff.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩
      intro mem
      have bad := sep x hit (z-x) (mem_filter.mp mem).1 z hz
      omega
    by_cases side' : v-(b-1)≤ x
    · apply mem_union_left
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨v-x,mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩,by omega⟩
      intro mem
      have bad := sep x hit (v-x) (mem_filter.mp mem).1 v hv
      omega
    · exact mem_union_right _ (mem_Ico.mpr ⟨by omega,by omega⟩)
  have back : R ⊆ Z := by
    intro x hx
    obtain ⟨hit,xl,xu⟩ := mem_filter.mp hx
    have gv := gap x hit
    have beyond := empty x hit (by omega)
    apply mem_image.mpr
    refine ⟨s-1-x,mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩,by omega⟩,by omega⟩
    intro mem
    have bad := sep x hit (s-1-x) (mem_filter.mp mem).1 (u+2*a) hU
    omega
  have upper := (card_le_card inc).trans (card_union_le (X ∪ Y) J)
  have upper' := card_union_le X Y
  have highCount := card_le_card back
  have cx : X.card ≤ H.card := card_image_le
  have cy : Y.card ≤ Hhi.card := card_image_le
  have cz : Z.card ≤ Hlo.card := card_image_le
  have cj : J.card=(v-(b-1))-(z-L+1) := Nat.card_Ico _ _
  have pl := prefix_partition T (show k≤ r by omega)
  have ph := prefix_partition T (show r≤ y by omega)
  change F T r=F T k+Q.card at pl
  change F T y=F T r+R.card at ph
  change a+F T k < D+F T y at sur
  change w+D=2*P.card at de
  omega



open Finset

theorem midpoint_ends {T : Finset ℕ} {a u : ℕ} (ha : a ∈ T) (hu : u ∈ T) (hs : u+2*a ∈ T)
    (pos : 0< a)
    (wide : ∀ z ∈ T, ∀ v ∈ T,z< u+a → u+a≤ v → z+a≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    ∃ z ∈ T, ∃ v ∈ T, u≤ z ∧ z< u+a ∧ u+a≤ v ∧ v≤ u+2*a ∧ z+a+2< v ∧
      (∀ x ∈ T,x< u+a → x≤ z) ∧ (∀ x ∈ T,u+a≤ x → v≤ x) ∧
      F T (z+1)=F T (u+a) ∧ F T v=F T (u+a) := by
  let P := T.filter (· < u+a)
  let Q := T.filter (u+a ≤ ·)
  have up : u ∈ P := mem_filter.mpr ⟨hu,by omega⟩
  have sq : u+2*a ∈ Q := mem_filter.mpr ⟨hs,by omega⟩
  let z := P.max' ⟨_,up⟩
  let v := Q.min' ⟨_,sq⟩
  have l : z ∈ T ∧ z< u+a := mem_filter.mp (max'_mem P ⟨_,up⟩)
  have r : v ∈ T ∧ u+a≤ v := mem_filter.mp (min'_mem Q ⟨_,sq⟩)
  have zl (x : ℕ) (hx : x ∈ T) (lo : x< u+a) : x≤ z := le_max' P x (mem_filter.mpr ⟨hx,lo⟩)
  have vh (x : ℕ) (hx : x ∈ T) (hi : u+a≤ x) : v≤ x := min'_le Q x (mem_filter.mpr ⟨hx,hi⟩)
  have span := wide z l.1 v r.1 l.2 r.2
  have exc := sep z l.1 a ha v r.1
  refine ⟨z,l.1,v,r.1,zl u hu (by omega),l.2,r.2,vh _ hs (by omega),by omega,zl,vh,?_,?_⟩
  · unfold F
    congr 1
    ext x
    simp only [mem_filter]
    exact ⟨fun ⟨hit,lo⟩ => ⟨hit,by omega⟩,fun ⟨hit,hi⟩ => ⟨hit,by have h := zl x hit hi; omega⟩⟩
  · unfold F
    congr 1
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hit,hi⟩
      refine ⟨hit,?_⟩
      by_contra! high
      exact (not_lt_of_ge (vh x hit high)) hi
    · rintro ⟨hit,lo⟩
      exact ⟨hit,by omega⟩

/-- The maximizing interval has discrepancy greater than half the
minimum. Integrality and the extra disallowed sums make the inequality
strict even at the integer endpoints. -/
theorem more_than_half {T : Finset ℕ} {a u L w D : ℕ} [DifferenceBounds T (u+2*a) D] (best : Maximizes T L w (u+2*a))
    (ha : a ∈ T) (hu : u ∈ T) (hs : u+2*a ∈ T) (pos : 0< a) (amin : ∀x ∈ T,a≤ x)
    (de : w+D=2*(window T L w).card)
    (wide : ∀ z ∈ T, ∀ v ∈ T,z< u+a → u+a≤ v → z+a≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (failed : u+a≤ F T u+F T (u+a)+F T (u+2*a)) : a< 2*D := by
  obtain ⟨z,hz,v,_,uz,zl,_,vh,big,_,_,zpop,vpop⟩ := midpoint_ends ha hu hs pos wide sep
  have az := amin z hz
  have low := interval_difference best de (fun x hx => pos.trans_le (amin x hx)) sep a (z+1) (by omega) (by omega)
  have empty : F T a=0 := by
    have h : T.filter (· < a)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt_of_ge (amin x (mem_filter.mp hx).1)) (mem_filter.mp hx).2
    simp [F,h]
  rw [empty,zpop] at low
  have high := discrepancy_prefix best de v (u+2*a) vh le_rfl
  rw [vpop] at high
  have middle := discrepancy_prefix best de (z+1-a) u (by omega) (by omega)
  omega



open Finset
open scoped Pointwise

theorem hole_room {T S : Finset ℕ} {l r : ℕ} (lr : l≤ r)
    (bound : ∀z ∈ S,l≤ z ∧ z< r ∧ z∉T) :
    S.card+F T r ≤ r-l+F T l := by
  let R := window T l (r-l)
  have dis : Disjoint S R := by
    apply disjoint_left.mpr
    intro x hx hr
    exact (bound x hx).2.2 (mem_filter.mp hr).1
  have inc : S ∪ R ⊆ Ico l r := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact mem_Ico.mpr ⟨(bound x h).1,(bound x h).2.1⟩
    · obtain ⟨_,lo,hi⟩ := mem_filter.mp h
      exact mem_Ico.mpr ⟨lo,by omega⟩
  have card := card_le_card inc
  rw [card_union_of_disjoint dis,Nat.card_Ico] at card
  have part := prefix_partition T lr
  change F T r=F T l+R.card at part
  omega

theorem shifted_room {T P : Finset ℕ} {L l r : ℕ} (lr : l≤ r) (hL : L ∈ T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,k+1 < i+j ∨ i+j+2 < k)
    (support : ∀x ∈ P,x ∈ T ∧ l≤ L+x ∧ L+x< r) :
    P.card+F T r ≤ r-l+F T l := by
  have holes := hole_room (T:=T) (S:=P.image (L+·)) lr (by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    obtain ⟨hit,lo,up⟩ := support i hi
    refine ⟨lo,up,?_⟩
    intro bad
    have f := sep L hL i hit (L+i) bad
    omega)
  rwa [card_image_of_injective _ (add_right_injective L)] at holes

/-- Three disjoint sum contributions and the middle gap. This is the
integer form of inequality (7) in Franchi–Gowers–Yip. -/
theorem three_translates {T : Finset ℕ} {a u L w c z : ℕ} (_ha : a ∈ T) (hs : u+2*a ∈ T)
    (hl : L ∈ T) (hr : L+w-1 ∈ T) (short : w< a) (wp : 0< w) (far : L+a< u)
    (cT : c ∈ T) (clow : c+L< u+a) (cg : ∀x ∈ T,x+L< u+a → x≤ c)
    (cjump : ∀x ∈ T,c< x → c+a+2< x)
    (uz : u≤ z) (_zm : z< u+a) (zp : z+a< c+(L+w)) (zjump : ∀x ∈ T,z< x → z+a+2< x)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,k+1 < i+j ∨ i+j+2 < k) :
    F T (u+2*a)+w+F T (u+2*a-L)+F T (L+a)+1 ≤
      2*a+F T u+F T (u-L)+F T (L+w) := by
  let b := L+w
  let s := u+2*a
  let y := s-L
  let r := u+a-L
  let k := u-L
  let j := z-L+1
  let m := min s (c+L+a+2)
  have eb : b=L+w := rfl
  have es : s=u+2*a := rfl
  have ey : y+L=s := by dsimp [y,s]; omega
  have er : r+L=u+a := by dsimp [r]; omega
  have ek : k+L=u := by dsimp [k]; omega
  have ej : L+j=z+1 := by dsimp [j]; omega
  have jm : z+1+w≤ m := by dsimp [m]; omega
  have ms : m≤ s := min_le_left _ _
  let A := window T k (j-k)
  let B := window T j (c+1-j)
  let C := window T r (y-r)
  let V := insert (b-1) (window T b (L+a-b))
  let K : Finset ℕ := {1,2}
  let S := (B+V)+K
  have early := shifted_room (P:=A) (show u≤ z+1 by omega) hl sep (by
    intro x hx
    obtain ⟨hit,lo,up⟩ := mem_filter.mp hx
    exact ⟨hit,by omega,by omega⟩)
  have late := shifted_room (P:=C) (show m≤ s by omega) hl sep (by
    intro x hx
    obtain ⟨hit,lo,up⟩ := mem_filter.mp hx
    have jump := cjump x hit (by omega)
    exact ⟨hit,by dsimp [m]; omega,by omega⟩)
  have ng : window T (z+1) w=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hit,lo,up⟩ := mem_filter.mp hx
    have v := zjump x hit (by omega)
    omega
  have same := partition_len T (z+1) w
  rw [ng,card_empty,add_zero] at same
  have bmem : c ∈ B := mem_filter.mpr ⟨cT,by omega,by omega⟩
  have bne : B.Nonempty := ⟨c,bmem⟩
  have vne : V.Nonempty := ⟨b-1,mem_insert_self _ _⟩
  have cd := cauchy_davenport_add_of_linearOrder_isCancelAdd bne vne
  have cd' := cauchy_davenport_add_of_linearOrder_isCancelAdd (bne.add vne) (show K.Nonempty from ⟨1,by simp [K]⟩)
  have cardK : K.card=2 := by decide
  change (B+V).card+K.card-1 ≤ S.card at cd'
  rw [cardK] at cd'
  have central := hole_room (S:=S) jm (T:=T) (by
    intro x hx
    obtain ⟨t,ht,e,he,eq⟩ := mem_add.mp hx
    obtain ⟨i,hi,v,hv,et⟩ := mem_add.mp ht
    obtain ⟨hit,lo,up⟩ := mem_filter.mp hi
    have vlim : v ∈ T ∧ b-1≤ v ∧ v< L+a := by
      rcases mem_insert.mp hv with rfl|h
      · exact ⟨hr,le_rfl,by omega⟩
      · obtain ⟨vT,vl,vu⟩ := mem_filter.mp h
        exact ⟨vT,by omega,by omega⟩
    have ev : e=1 ∨ e=2 := by simpa [K] using he
    have avoid := sep i hit v vlim.1 (u+2*a) hs
    refine ⟨by omega,by dsimp [m]; omega,?_⟩
    intro xt
    have f := sep i hit v vlim.1 x xt
    omega)
  have aCt := prefix_partition T (show k≤ j by omega)
  have bCt := prefix_partition T (show j≤ c+1 by omega)
  have cCt := prefix_partition T (show r≤ y by omega)
  have vCt := prefix_partition T (show b≤ L+a by omega)
  change F T j=F T k+A.card at aCt
  change F T (c+1)=F T j+B.card at bCt
  change F T y=F T r+C.card at cCt
  have miss : b-1∉window T b (L+a-b) := by
    intro h
    have h := (mem_filter.mp h).2.1
    omega
  have vc : V.card=(window T b (L+a-b)).card+1 := card_insert_of_notMem miss
  have sameC : F T r=F T (c+1) := by
    unfold F
    congr 1
    ext x
    simp only [mem_filter]
    exact ⟨fun ⟨hit,lo⟩ => ⟨hit,by have z := cg x hit (by omega); omega⟩,
      fun ⟨hit,lo⟩ => ⟨hit,by omega⟩⟩
  change F T s+w+F T y+F T (L+a)+1 ≤ 2*a+F T u+F T k+F T b
  omega



open Finset

theorem growth_upper (T : Finset ℕ) {i j : ℕ} (ij : i≤ j) :
    F T j ≤ F T i+(j-i) := by
  have s := prefix_partition T ij
  have sub : window T i (j-i) ⊆ Ico i j := by
    intro x hx
    obtain ⟨_,lo,hi⟩ := mem_filter.mp hx
    exact mem_Ico.mpr ⟨lo,by omega⟩
  have b := card_le_card sub
  rw [Nat.card_Ico] at b
  omega

theorem wing_mass {T : Finset ℕ} {a u L w D g : ℕ} [DifferenceBounds T (u+2*a) D] (best : Maximizes T L w (u+2*a))
    (_ha : a ∈ T) (amin : ∀x ∈ T,a≤ x) (pos : 0< a) (large : 2*a< L)
    (short : w< a) (far : L+a< u)
    (de : w+D=2*(window T L w).card)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (slack : 2*F T (u-L)+F T u+g = u-L-a+F T (L+a))
    (translates : F T (u+2*a)+w+F T (u+2*a-L)+F T (L+a)+1 ≤
      2*a+F T u+F T (u-L)+F T (L+w))
    (mass : F T u+2*F T (u+a)≤ u+D)
    (failed : u+a≤ F T u+F T (u+a)+F T (u+2*a)) :
    a+g+2*w+F T (L-2*a)+2 ≤ 2*D+F T L+(window T L w).card := by
  let y := u+2*a-L
  have ey : y+L=u+2*a := by dsimp [y]; omega
  have diff := interval_difference best de (fun i hi => pos.trans_le (amin i hi))
    sep y u (by omega) (by omega)
  rw [show u-y=L-2*a by omega] at diff
  have mon := le_prefix T (show L+w≤ L+a by omega)
  have q := partition_len T L w
  change F T (u+2*a)+w+F T y+F T (L+a)+1 ≤ 2*a+F T u+F T (u-L)+F T (L+w) at translates
  omega

theorem right_wing_cap {T : Finset ℕ} {a L w : ℕ} (ha : a ∈ T) (large : 2*a< L) (short : w< a)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    F T L+(window T L w).card ≤ a+F T (L-a) := by
  have p := paired T a (L-a) w (fun x hx hit => by have b := sep x hx a ha (x+a) hit; omega)
  rw [show L-a+a=L by omega] at p
  have s := partition_len T (L-a) w
  have g := growth_upper T (show L-a+w≤ L by omega)
  omega

/-- An occupied point in the wing before the maximum provides an opposing
prefix bound, the discrete counterpart of inequality (9) in FGY. -/
theorem wing_witness {T : Finset ℕ} {a L w D g : ℕ} (ha : a ∈ T) (hL : L ∈ T) (amin : ∀x ∈ T,a≤ x)
    (large : 2*a< L) (short : w< a)
    (de : w+D=2*(window T L w).card)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (mass : a+g+2*w+F T (L-2*a)+2 ≤ 2*D+F T L+(window T L w).card) :
    ∃ v ∈ T, L-2*a≤ v ∧ v< L-a ∧ (∀ x ∈ T,L-2*a≤ x → x< L-a → x≤ v) ∧
      F T L+F T (L-v) ≤ a+F T (L-2*a) := by
  let l := L-2*a
  let r := L-a
  let P := window T l (r-l)
  have lr : l≤ r := by dsimp [l,r]; omega
  have part := prefix_partition T lr
  change F T r=F T l+P.card at part
  have qle : (window T L w).card ≤ w := by
    have sb : window T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card sb
  have lim := right_wing_cap ha large short sep
  change F T L+(window T L w).card ≤ a+F T r at lim
  change a+g+2*w+F T l+2 ≤ 2*D+F T L+(window T L w).card at mass
  have positive : P.Nonempty := card_pos.mp (by omega)
  let v := P.max' positive
  have mv := max'_mem P positive
  obtain ⟨hit,lo,hi⟩ := mem_filter.mp mv
  have vu : v< r := by omega
  have vl : l≤ v := lo
  have greatest (x : ℕ) (hx : x ∈ T) (lx : l≤ x) (xr : x< r) : x≤ v :=
    le_max' P x (mem_filter.mpr ⟨hx,lx,by omega⟩)
  refine ⟨v,hit,vl,vu,greatest,?_⟩
  have ve : F T r=F T (v+1) := by
    unfold F
    congr 1
    ext x
    simp only [mem_filter]
    have cheap (hx : x< l) : x≤ v := by omega
    constructor
    · rintro ⟨xt,up⟩
      by_cases low : x< l
      · exact ⟨xt,by have h := cheap low; omega⟩
      · exact ⟨xt,by have h := greatest x xt (by omega) up; omega⟩
    · rintro ⟨xt,up⟩
      exact ⟨xt,by omega⟩
  have ee : l+a=r := by dsimp [l,r]; omega
  have rr : v+1+a≤ L := by dsimp [r] at vu; omega
  have p := paired T a l (v+1-l) (fun i hi bad => by have h := sep i hi a ha (i+a) bad; omega)
  rw [ee] at p
  have first := prefix_partition T (show l≤ v+1 by omega)
  have next := partition_len T r (v+1-l)
  rw [show r+(v+1-l)=v+1+a by omega] at next
  let B := T.filter (· < L-v)
  let C := B.image (fun x => v+1+x)
  have cardC : C.card=F T (L-v) := card_image_of_injective B (add_right_injective (v+1))
  have zr := hole_room (T:=T) (S:=C) rr (by
    intro z hz
    obtain ⟨x,hx,eq⟩ := mem_image.mp hz
    have it := (mem_filter.mp hx).1; have upper := (mem_filter.mp hx).2
    have al := amin x it
    have fend := sep v hit x it L hL
    change v+1+x=z at eq
    refine ⟨by omega,by omega,?_⟩
    intro zt
    have h := sep v hit x it z zt
    omega)
  rw [cardC] at zr
  change F T L+F T (L-v) ≤ a+F T l
  omega



open Finset

theorem slack_at {T : Finset ℕ} {a u L w g c j : ℕ} (best : Maximizes T L w (u+2*a))
    (_ha : a ∈ T) (hu : u ∈ T) (hL : L ∈ T) (hc : c ∈ T)
    (amin : ∀ x ∈ T,a≤ x) (far : L+a< u)
    (shift : c≤ j ∧ j≤ c+1) (fits : j+w≤ u-L)
    (slack : 2*F T (u-L)+F T u+g=u-L-a+F T (L+a))
    (sep : ∀ i ∈ T, ∀ v ∈ T, ∀ z ∈ T,z+1 < i+v ∨ i+v+2 < z) :
    (window T L w).card ≤ g+F T j+2*(window T j w).card := by
  let k := u-L
  have ek : L+k=u := by dsimp [k]; omega
  have aj := amin c hc
  have marks (x : ℕ) (h : L+x ∈ T) (xu : x≤ u+2*a) :
      x∉T ∧ ∀ s n,s+n=x → disc T s n ≤ 0 := by
    refine ⟨?_,suffix_nonpositive_of_sum best xu h sep⟩
    intro xt
    have bad := sep L hL x xt (L+x) h
    omega
  have lower := doubled_with_defect marks a (j-a) (by omega) (F T j)
    (fun s n he => sparse_end (le_refl (F T j)) s n (by omega))
  have low1 := prefix_partition T (show a≤ j by omega)
  have low2 := partition_len T (L+a) (j-a)
  rw [show L+a+(j-a)=L+j by omega] at low2
  have zero : F T a=0 := by
    have nil : T.filter (· < a)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt_of_ge (amin x (mem_filter.mp hx).1)) (mem_filter.mp hx).2
    simp [F,nil]
  have right := anchored_window best hL sep (show j+w≤ k by omega) (by omega) (ek ▸ hu)
  rw [ek] at right
  let Q := window T L w
  let V := Q.image (j+·)
  have vc : V.card=Q.card := card_image_of_injective _ (add_right_injective j)
  have central := hole_room (T:=T) (S:=V) (show L+j≤ L+(j+w) by omega) (by
    intro x hx
    obtain ⟨i,hi,e⟩ := mem_image.mp hx
    obtain ⟨hit,lo,up⟩ := mem_filter.mp hi
    change j+i=x at e
    refine ⟨by omega,by omega,?_⟩
    intro bad
    have broken := sep c hc i hit x bad
    omega)
  rw [vc] at central
  have pop := partition_len T j w
  change 2*F T k+F T u+g=k-a+F T (L+a) at slack
  change Q.card ≤ g+F T j+2*(window T j w).card
  omega

theorem last_prefix {T : Finset ℕ} {a x : ℕ} (ha : a ∈ T) (ax : a< x) :
    ∃ c ∈ T,c< x ∧ (∀ z ∈ T,z< x → z≤ c) ∧ F T (c+1)=F T x := by
  let P := T.filter (· < x)
  have ne : P.Nonempty := ⟨a,mem_filter.mpr ⟨ha,ax⟩⟩
  let c := P.max' ne
  have hit := mem_filter.mp (max'_mem P ne)
  have bound (z : ℕ) (hz : z ∈ T) (lo :z< x) : z≤ c := le_max' P z (mem_filter.mpr ⟨hz,lo⟩)
  refine ⟨c,hit.1,hit.2,bound,?_⟩
  unfold F
  congr 1
  ext z
  simp only [mem_filter]
  exact ⟨fun ⟨zt,zl⟩ => ⟨zt,by have cc : c< x := hit.2; omega⟩,
    fun ⟨zt,zl⟩ => ⟨zt,by have zc := bound z zt zl; omega⟩⟩

/-- A counterexample could only place the scaled parameter y strictly
between three minima and three minima plus the width of the maximum. -/
theorem narrow_regime {T : Finset ℕ} {a u L w g D : ℕ} (best : Maximizes T L w (u+2*a))
    (ha : a ∈ T) (hu : u ∈ T) (hL : L ∈ T) (hR : L+w-1 ∈ T)
    (amin : ∀x ∈ T,a≤ x) (large : 2*a< L) (short : w< a) (wp : 0< w) (far : L+a< u)
    (de : w+D=2*(window T L w).card)
    (slack : 2*F T (u-L)+F T u+g=u-L-a+F T (L+a))
    (mass : a+g+2*w+F T (L-2*a)+2 ≤ 2*D+F T L+(window T L w).card)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    u< L+a+w := by
  obtain ⟨v,hv,vl,vr,_,order⟩ := wing_witness ha hL amin large short de sep mass
  let k := u-L
  let d := L-v
  let Q := window T L w
  have ek : k+L=u := by dsimp [k]; omega
  have ed : d+v=L := by dsimp [d]; omega
  have ad : a< d := by omega
  have cap : Q.card≤ w := by
    have inc : Q ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card inc
  change F T L+F T d ≤ a+F T (L-2*a) at order
  change w+D=2*Q.card at de
  change a+g+2*w+F T (L-2*a)+2 ≤ 2*D+F T L+Q.card at mass
  have first : k< d+w := by
    by_contra! farK
    obtain ⟨c,hc,before,upper,cpop⟩ := last_prefix ha ad
    let B := window T (c+1) w
    have pack := shifted_room (P:=B) (show L≤ L+w by omega) hv sep (by
      intro x hx
      obtain ⟨xt,xl,xu⟩ := mem_filter.mp hx
      have beyond : d≤ x := by by_contra! prior; have bad := upper x xt prior; omega
      exact ⟨xt,by omega,by omega⟩)
    have eq := partition_len T L w
    change F T (L+w)=F T L+Q.card at eq
    have boost := slack_at best ha hu hL hc amin far (show c≤ c+1 ∧ c+1≤ c+1 by omega)
      (by omega) slack sep
    change Q.card ≤ g+F T (c+1)+2*B.card at boost
    omega
  by_contra! outside
  have much : a < k-w := by
    have avoid := sep (L+w-1) hR a ha u hu
    omega
  obtain ⟨c,hc,cl,upper,cpop⟩ := last_prefix ha much
  let B := window T (c+1) w
  have order2 := le_prefix T (show k-w≤ d by omega)
  have pack := reflected_disjoint_count (P:=B) (M:=u-1) (l:=L) (r:=L+w) (by omega)
    (by intro x hx; have hi := (mem_filter.mp hx).2.2; omega) (by
      intro x hx
      obtain ⟨xt,xl,xu⟩ := mem_filter.mp hx
      have beyond : k-w≤ x := by by_contra! prior; have bad := upper x xt prior; omega
      refine ⟨by omega,by omega,?_⟩
      intro hit
      have bad := sep x xt (u-1-x) hit u hu
      omega)
  have eq := partition_len T L w
  change F T (L+w)=F T L+Q.card at eq
  have boost := slack_at best ha hu hL hc amin far (show c≤ c+1 ∧ c+1≤ c+1 by omega)
    (by omega) slack sep
  change Q.card ≤ g+F T (c+1)+2*B.card at boost
  omega



open Finset

theorem surviving_regime {T : Finset ℕ} {a u L w D : ℕ} [DifferenceBounds T (u+2*a) D] (best : Maximizes T L w (u+2*a))
    (ha : a ∈ T) (hu : u ∈ T) (hs : u+2*a ∈ T)
    (amin : ∀x ∈ T,a≤ x) (large : 2*a< L) (start : L< u) (inside : L+w< u+a)
    (hL : L ∈ T) (hR : L+w-1 ∈ T) (short : w< a) (wp : 0< w)
    (de : w+D=2*(window T L w).card) (mass : F T u+2*F T (u+a)≤ u+D)
    (gap : ∀ t ∈ T,t+L< u+a ∨ u+2*a< t+L+w)
    (width : ∀ t ∈ T, ∀ v ∈ T,t+L< u+a → u+a≤ v+L → t+a≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (failed : u+a≤ F T u+F T (u+a)+F T (u+2*a)) :
    ∃ g c z, L+a< u ∧ u< L+a+w ∧ a< 2*D ∧ c ∈ T ∧ c+L< u+a ∧
      (∀ x ∈ T,x+L< u+a → x≤ c) ∧ (∀ x ∈ T, c< x → c+a+2< x) ∧
      z ∈ T ∧ u≤ z ∧ z< u+a ∧ z+a< c+(L+w) ∧
      (∀ x ∈ T,x< u+a → x≤ z) ∧ (∀ x ∈ T,z< x → z+a+2< x) ∧
      2*F T (u-L)+F T u+g=u-L-a+F T (L+a) ∧
      5*a+2*g+4*F T (u-L)≤ 5*D+4*F T (u+2*a-L) ∧
      a+g+2*w+F T (L-2*a)+2≤ 2*D+F T L+(window T L w).card := by
  have pos : 0< a := by omega
  have far := far_left best ha hu hs amin start inside hL hR short wp de mass gap width sep failed
  obtain ⟨g,slack,extra⟩ := surplus best hu amin pos hL large far de mass sep failed
  have cap : (window T L w).card ≤ w := by
    have sub : window T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card sub
  have gain : a+F T (u-L)< D+F T (u+2*a-L) := by omega
  obtain ⟨c,hc,cl,cg,cn⟩ := last_before ha start width sep
  have prior := no_middle_mark large far short wp ha hu hs de gap cl cg sep gain
  have middle := central_width far short wp hs de gap cl cg cn prior sep gain
  obtain ⟨z,hz,v,hv,uz,zl,vh,vs,dist,zmax,vmin,zcard,vcard⟩ := midpoint_ends ha hu hs pos middle sep
  have lz := prior z hz zl.le
  have zn (x : ℕ) (hit : x ∈ T) (beyond : z< x) : z+a+2< x := by
    have reach : u+a≤ x := by by_contra! before; have zz := zmax x hit before; omega
    have bound := vmin x hit reach
    omega
  have higher := more_than_half best ha hu hs pos amin de middle sep failed
  have pieces := three_translates ha hs hL hR short wp far hc cl cg cn uz zl lz zn sep
  have wing := wing_mass best ha amin pos large short far de sep slack pieces mass failed
  have upper := narrow_regime best ha hu hL hR amin large short wp far de slack wing sep
  exact ⟨g,c,z,far,upper,higher,hc,cl,cg,cn,hz,uz,zl,lz,zmax,zn,slack,extra,wing⟩


end GreenLocal
open GreenLocal Finset

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1_H3_R1.H2 := by
  intro T a u L w D ha hu hs amin high lu inside hL hR short wp best eq mass gap wide sep dif failed
  let _ : DifferenceBounds T (u+2*a) D := ⟨dif⟩
  have mx : Maximizes T L w (u+2*a) := ⟨by omega,by
    intro p n hi
    have b := best p n hi
    unfold disc window
    omega⟩
  exact surviving_regime mx ha hu hs amin high lu inside hL hR short wp eq mass gap wide sep failed

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H2

namespace GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H3

/- Discrete proof of the final steps in Franchi–Gowers–Yip, arXiv:2607.06073,
Sections 4.9–4.11. Two reflected translates bound the prefix before the
maximizing block. An enlarged difference set puts the last occupied cell
of the central gap below twice the minimum. The resulting prefix bounds
contradict the assumed failure of the three-prefix inequality. -/
namespace GreenFinalLocal
open Finset
open scoped Pointwise

def window (T : Finset ℕ) (l w : ℕ) := T.filter (fun x => l ≤ x ∧ x < l+w)

def disc (T : Finset ℕ) (l w : ℕ) : ℤ := 2*((window T l w).card:ℤ) - w

theorem card_split (T : Finset ℕ) (l p q : ℕ) :
    (window T l (p+q)).card = (window T l p).card + (window T (l+p) q).card := by
  classical
  have split : window T l (p+q) = window T l p ∪ window T (l+p) q := by
    ext x
    simp only [window,mem_filter,mem_union]
    constructor
    · rintro ⟨h,lo,hi⟩
      by_cases test : x < l+p
      · exact Or.inl ⟨h,lo,test⟩
      · exact Or.inr ⟨h,by omega,by omega⟩
    · rintro (⟨h,lo,hi⟩ | ⟨h,lo,hi⟩) <;> exact ⟨h,by omega,by omega⟩
  have dis : Disjoint (window T l p) (window T (l+p) q) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨_,_,hi⟩ := mem_filter.mp hx
    obtain ⟨_,lo,_⟩ := mem_filter.mp hy
    omega
  rw [split,card_union_of_disjoint dis]

theorem paired (T : Finset ℕ) (h l w : ℕ)
    (noPair : ∀ x ∈ T, x+h ∉ T) :
    (window T l w).card + (window T (l+h) w).card ≤ w := by
  let A := (window T l w).image (·+h)
  let B := window T (l+h) w
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact noPair x (mem_filter.mp hx).1 (mem_filter.mp hb).1
  have sub : A ∪ B ⊆ Ico (l+h) (l+h+w) := by
    intro z hz
    rcases mem_union.mp hz with hA | hB
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hA
      obtain ⟨_,lo,hi⟩ := mem_filter.mp hx
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · exact mem_Ico.mpr (mem_filter.mp hB).2
  have b := card_le_card sub
  rw [card_union_of_disjoint dis,Nat.card_Ico] at b
  have c : A.card = (window T l w).card := card_image_of_injective _ (add_left_injective h)
  rw [c] at b
  dsimp [B] at b
  omega

theorem disc_split (T : Finset ℕ) (l p q : ℕ) :
    disc T l (p+q) = disc T l p + disc T (l+p) q := by
  simp only [disc,card_split,Nat.cast_add]
  ring

def Maximizes (T : Finset ℕ) (L w U : ℕ) : Prop :=
  L+w ≤ U ∧ ∀ s n : ℕ, s+n ≤ U → disc T s n ≤ disc T L w

theorem balanced_ends {T : Finset ℕ} {L w U : ℕ} (maximal : Maximizes T L w U)
    (k : ℕ) (kw : k ≤ w) : 0 ≤ disc T L k ∧ 0 ≤ disc T (L+(w-k)) k := by
  obtain ⟨inside,bound⟩ := maximal
  have e1 : k+(w-k)=w := by omega
  have e2 : w-k+k=w := by omega
  have e := disc_split T L k (w-k)
  have f := disc_split T L (w-k) k
  rw [e1] at e
  rw [e2] at f
  have b := bound (L+k) (w-k) (by omega)
  have c := bound L (w-k) (by omega)
  omega

theorem mirror_pair {T : Finset ℕ} {l m n : ℕ}
    (forbid : ∀ x ∈ T, ∀ y ∈ T, x+y+1 ≠ l+m+n) :
    disc T l n + disc T m n ≤ 0 := by
  let f (x : ℕ) := l+m+n-1-x
  let A := (window T l n).image f
  let B := window T m n
  have inj : A.card = (window T l n).card := by
    apply card_image_of_injOn
    intro x hx y hy e
    obtain ⟨_,xl,xu⟩ := mem_filter.mp hx
    obtain ⟨_,yl,yu⟩ := mem_filter.mp hy
    dsimp [f] at e
    omega
  have dis : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz hb
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨xt,xl,xu⟩ := mem_filter.mp hx
    have yt := (mem_filter.mp hb).1
    apply forbid x xt _ yt
    dsimp [f]
    omega
  have sub : A ∪ B ⊆ Ico m (m+n) := by
    intro z hz
    rcases mem_union.mp hz with ha | hb
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
      obtain ⟨_,xl,xu⟩ := mem_filter.mp hx
      dsimp [f]
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · exact mem_Ico.mpr (mem_filter.mp hb).2
  have card := card_le_card sub
  rw [card_union_of_disjoint dis,inj,Nat.card_Ico] at card
  dsimp [B] at card
  unfold disc
  omega

theorem suffix_nonpositive_of_sum {T : Finset ℕ} {L w U z : ℕ}
    (maximal : Maximizes T L w U) (endBound : z ≤ U) (anchor : L+z ∈ T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (s k : ℕ) (ends : s+k = z) : disc T s k ≤ 0 := by
  have avoid (q n : ℕ) (eq : q+n=z) : disc T L n + disc T q n ≤ 0 := by
    apply mirror_pair
    intro x hx y hy bad
    have h := sep x hx y hy _ anchor
    omega
  by_cases small : k ≤ w
  · have left := (balanced_ends maximal k small).1
    have pair := avoid s k ends
    omega
  · have len : k-w+w=k := by omega
    have split := disc_split T s (k-w) w
    rw [len] at split
    have first := maximal.2 s (k-w) (by omega)
    have last := avoid (s+(k-w)) w (by omega)
    omega

theorem suffix_nonpositive_of_difference {T : Finset ℕ} {L w U z : ℕ}
    (maximal : Maximizes T L w U) (endBound : z ≤ U) (ordered : z ≤ L+w)
    (absent : ∀ x ∈ T, x+(L+w-z) ∉ T)
    (s k : ℕ) (ends : s+k=z) : disc T s k ≤ 0 := by
  let h := L+w-z
  have pair (q n : ℕ) : disc T q n + disc T (q+h) n ≤ 0 := by
    have b := paired T h q n absent
    unfold disc
    omega
  by_cases small : k ≤ w
  · have eq : s+h = L+(w-k) := by dsimp [h]; omega
    have b := pair s k
    rw [eq] at b
    have right := (balanced_ends maximal k small).2
    omega
  · have len : k-w+w=k := by omega
    have split := disc_split T s (k-w) w
    rw [len] at split
    have first := maximal.2 s (k-w) (by omega)
    have eq : s+(k-w)+h = L := by dsimp [h]; omega
    have last := pair (s+(k-w)) w
    rw [eq] at last
    omega

theorem one_cell (T : Finset ℕ) (s : ℕ) :
    (window T s 1).card = if s ∈ T then 1 else 0 := by
  classical
  by_cases hs : s ∈ T
  · have eq : window T s 1 = {s} := by
      ext x
      simp only [window,mem_filter,mem_singleton]
      constructor
      · rintro ⟨_,l,r⟩; omega
      · rintro rfl; exact ⟨hs,le_rfl,by omega⟩
    simp [eq,hs]
  · have eq : window T s 1 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨xt,lo,hi⟩ := mem_filter.mp hx
      have e : x=s := by omega
      exact hs (e ▸ xt)
    simp [eq,hs]

theorem doubled_with_defect {T A : Finset ℕ} {L U : ℕ}
    (marks : ∀ x, L+x ∈ A → x ≤ U →
      x ∉ T ∧ ∀ t k, t+k=x → disc T t k ≤ 0)
    (s n : ℕ) (inside : s+n ≤ U)
    (H : ℕ) (goodEnd : ∀ t k : ℕ, t+k=s+n → disc T t k ≤ H) :
    2*(window T s n).card + (window A (L+s) n).card ≤ n+H := by
  induction n using Nat.strong_induction_on generalizing s H with
  | h n ih =>
    by_cases empty : window A (L+s) n = ∅
    · have b := goodEnd s n rfl
      unfold disc at b
      rw [empty,card_empty]
      omega
    obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨xt,xl,xr⟩ := mem_filter.mp hx
    let k := x-(L+s)
    let m := n-k-1
    have eq : x = L+(s+k) := by dsimp [k]; omega
    have kn : k< n := by dsimp [k]; omega
    have endEq : k+(1+m)=n := by dsimp [m]; omega
    have hit : L+(s+k) ∈ A := eq ▸ xt
    obtain ⟨miss,reset⟩ := marks (s+k) hit (by omega)
    have first := ih k kn s (by omega) 0 (by simpa using reset)
    have second := ih m (by omega) (s+k+1) (by omega) H
      (fun t len ends => goodEnd t len (by omega))
    have share (P : Finset ℕ) (z : ℕ) :
        (window P z n).card = (window P z k).card + (window P (z+k) 1).card +
          (window P (z+k+1) m).card := by
      have a := card_split P z k (1+m)
      have b := card_split P (z+k) 1 m
      rw [endEq,b] at a
      omega
    have low := share T s
    have high := share A (L+s)
    rw [one_cell,if_neg miss] at low
    have sumEq : L+s+k=L+(s+k) := by omega
    have sumEq' : L+(s+k)+1=L+(s+k+1) := by omega
    rw [one_cell,sumEq,sumEq',if_pos hit] at high
    omega

theorem near_right {T : Finset ℕ} {a u L w : ℕ} (ha : a ∈ T) (hu : u ∈ T)
    (hL : L ∈ T) (hR : L+w-1 ∈ T) (aL : a ≤ L) (short : w< a) (_wp : 0< w)
    (width : ∀ t ∈ T, ∀ v ∈ T,t+L < u+a → u+a ≤ v+L → t+a ≤ v)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (near : u< L+w+a) : u+a ≤ L+L := by
  by_contra! before
  have rprior : L+w-1+L< u+a := by
    by_contra! after
    have h := width L hL (L+w-1) hR before after
    omega
  have h := width (L+w-1) hR u hu rprior (by omega)
  have avoid := sep (L+w-1) hR a ha u hu
  omega

def F (T : Finset ℕ) (j : ℕ) := (T.filter (· < j)).card

theorem prefix_partition (T : Finset ℕ) {p q : ℕ} (ord : p ≤ q) :
    F T q = F T p+(window T p (q-p)).card := by
  have split := card_split T 0 p (q-p)
  have pref (j : ℕ) : window T 0 j=T.filter (· < j) := by
    ext x
    simp [window]
  rw [show p+(q-p)=q by omega,pref,pref,Nat.zero_add] at split
  exact split

theorem partition_len (T : Finset ℕ) (p n : ℕ) :
    F T (p+n)=F T p+(window T p n).card := by
  have s := prefix_partition T (Nat.le_add_right p n)
  rwa [Nat.add_sub_cancel_left] at s

theorem le_prefix (T : Finset ℕ) {p q : ℕ} (ord : p ≤ q) : F T p ≤ F T q :=
  card_le_card (fun _ hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.trans_le ord⟩)

theorem anchored_window {T : Finset ℕ} {L w U : ℕ} (best : Maximizes T L w U)
    (hL : L ∈ T) (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    {p q : ℕ} (pq : p≤ q) (qu : q≤ U) (hit : L+q ∈ T) :
    2*F T q+F T (L+q) ≤ q-p+2*F T p+F T (L+p) := by
  have marks (x : ℕ) (h : L+x ∈ T) (xu : x≤ U) :
      x∉T ∧ ∀ j n,j+n=x → disc T j n ≤ 0 := by
    refine ⟨?_,suffix_nonpositive_of_sum best xu h sep⟩
    intro xt
    have bad := sep L hL x xt (L+x) h
    omega
  have h := doubled_with_defect marks p (q-p) (by omega) 0
    (fun j n eq => suffix_nonpositive_of_sum best qu hit sep j n (by omega))
  have p1 := prefix_partition T pq
  have p2 := partition_len T (L+p) (q-p)
  rw [show L+p+(q-p)=L+q by omega] at p2
  omega

theorem hole_room {T S : Finset ℕ} {l r : ℕ} (lr : l≤ r)
    (bound : ∀z ∈ S,l≤ z ∧ z< r ∧ z∉T) :
    S.card+F T r ≤ r-l+F T l := by
  let R := window T l (r-l)
  have dis : Disjoint S R := by
    apply disjoint_left.mpr
    intro x hx hr
    exact (bound x hx).2.2 (mem_filter.mp hr).1
  have inc : S ∪ R ⊆ Ico l r := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · exact mem_Ico.mpr ⟨(bound x h).1,(bound x h).2.1⟩
    · obtain ⟨_,lo,hi⟩ := mem_filter.mp h
      exact mem_Ico.mpr ⟨lo,by omega⟩
  have card := card_le_card inc
  rw [card_union_of_disjoint dis,Nat.card_Ico] at card
  have part := prefix_partition T lr
  change F T r=F T l+R.card at part
  omega

theorem shifted_room {T P : Finset ℕ} {L l r : ℕ} (lr : l≤ r) (hL : L ∈ T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,k+1 < i+j ∨ i+j+2 < k)
    (support : ∀x ∈ P,x ∈ T ∧ l≤ L+x ∧ L+x< r) :
    P.card+F T r ≤ r-l+F T l := by
  have holes := hole_room (T:=T) (S:=P.image (L+·)) lr (by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    obtain ⟨hit,lo,up⟩ := support i hi
    refine ⟨lo,up,?_⟩
    intro bad
    have f := sep L hL i hit (L+i) bad
    omega)
  rwa [card_image_of_injective _ (add_right_injective L)] at holes

theorem growth_upper (T : Finset ℕ) {i j : ℕ} (ij : i≤ j) :
    F T j ≤ F T i+(j-i) := by
  have s := prefix_partition T ij
  have sub : window T i (j-i) ⊆ Ico i j := by
    intro x hx
    obtain ⟨_,lo,hi⟩ := mem_filter.mp hx
    exact mem_Ico.mpr ⟨lo,by omega⟩
  have b := card_le_card sub
  rw [Nat.card_Ico] at b
  omega

theorem right_wing_cap {T : Finset ℕ} {a L w : ℕ} (ha : a ∈ T) (large : 2*a< L) (short : w< a)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    F T L+(window T L w).card ≤ a+F T (L-a) := by
  have p := paired T a (L-a) w (fun x hx hit => by have b := sep x hx a ha (x+a) hit; omega)
  rw [show L-a+a=L by omega] at p
  have s := partition_len T (L-a) w
  have g := growth_upper T (show L-a+w≤ L by omega)
  omega

theorem wing_witness {T : Finset ℕ} {a L w D g : ℕ} (ha : a ∈ T) (hL : L ∈ T) (amin : ∀x ∈ T,a≤ x)
    (large : 2*a< L) (short : w< a)
    (de : w+D=2*(window T L w).card)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l)
    (mass : a+g+2*w+F T (L-2*a)+2 ≤ 2*D+F T L+(window T L w).card) :
    ∃ v ∈ T, L-2*a≤ v ∧ v< L-a ∧ (∀ x ∈ T,L-2*a≤ x → x< L-a → x≤ v) ∧
      F T L+F T (L-v) ≤ a+F T (L-2*a) := by
  let l := L-2*a
  let r := L-a
  let P := window T l (r-l)
  have lr : l≤ r := by dsimp [l,r]; omega
  have part := prefix_partition T lr
  change F T r=F T l+P.card at part
  have qle : (window T L w).card ≤ w := by
    have sb : window T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card sb
  have lim := right_wing_cap ha large short sep
  change F T L+(window T L w).card ≤ a+F T r at lim
  change a+g+2*w+F T l+2 ≤ 2*D+F T L+(window T L w).card at mass
  have positive : P.Nonempty := card_pos.mp (by omega)
  let v := P.max' positive
  have mv := max'_mem P positive
  obtain ⟨hit,lo,hi⟩ := mem_filter.mp mv
  have vu : v< r := by omega
  have vl : l≤ v := lo
  have greatest (x : ℕ) (hx : x ∈ T) (lx : l≤ x) (xr : x< r) : x≤ v :=
    le_max' P x (mem_filter.mpr ⟨hx,lx,by omega⟩)
  refine ⟨v,hit,vl,vu,greatest,?_⟩
  have ve : F T r=F T (v+1) := by
    unfold F
    congr 1
    ext x
    simp only [mem_filter]
    have cheap (hx : x< l) : x≤ v := by omega
    constructor
    · rintro ⟨xt,up⟩
      by_cases low : x< l
      · exact ⟨xt,by have h := cheap low; omega⟩
      · exact ⟨xt,by have h := greatest x xt (by omega) up; omega⟩
    · rintro ⟨xt,up⟩
      exact ⟨xt,by omega⟩
  have ee : l+a=r := by dsimp [l,r]; omega
  have rr : v+1+a≤ L := by dsimp [r] at vu; omega
  have p := paired T a l (v+1-l) (fun i hi bad => by have h := sep i hi a ha (i+a) bad; omega)
  rw [ee] at p
  have first := prefix_partition T (show l≤ v+1 by omega)
  have next := partition_len T r (v+1-l)
  rw [show r+(v+1-l)=v+1+a by omega] at next
  let B := T.filter (· < L-v)
  let C := B.image (fun x => v+1+x)
  have cardC : C.card=F T (L-v) := card_image_of_injective B (add_right_injective (v+1))
  have zr := hole_room (T:=T) (S:=C) rr (by
    intro z hz
    obtain ⟨x,hx,eq⟩ := mem_image.mp hz
    have it := (mem_filter.mp hx).1; have upper := (mem_filter.mp hx).2
    have al := amin x it
    have fend := sep v hit x it L hL
    change v+1+x=z at eq
    refine ⟨by omega,by omega,?_⟩
    intro zt
    have h := sep v hit x it z zt
    omega)
  rw [cardC] at zr
  change F T L+F T (L-v) ≤ a+F T l
  omega

theorem last_prefix {T : Finset ℕ} {a x : ℕ} (ha : a ∈ T) (ax : a< x) :
    ∃ c ∈ T,c< x ∧ (∀ z ∈ T,z< x → z≤ c) ∧ F T (c+1)=F T x := by
  let P := T.filter (· < x)
  have ne : P.Nonempty := ⟨a,mem_filter.mpr ⟨ha,ax⟩⟩
  let c := P.max' ne
  have hit := mem_filter.mp (max'_mem P ne)
  have bound (z : ℕ) (hz : z ∈ T) (lo :z< x) : z≤ c := le_max' P z (mem_filter.mpr ⟨hz,lo⟩)
  refine ⟨c,hit.1,hit.2,bound,?_⟩
  unfold F
  congr 1
  ext z
  simp only [mem_filter]
  exact ⟨fun ⟨zt,zl⟩ => ⟨zt,by have cc : c< x := hit.2; omega⟩,
    fun ⟨zt,zl⟩ => ⟨zt,by have zc := bound z zt zl; omega⟩⟩

theorem twice_wing_mass {T : Finset ℕ} {a L w g D : ℕ} (ha : a ∈ T)
    (large : 2*a< L) (short : w< a) (de : w+D=2*(window T L w).card)
    (mass : a+g+2*w+F T (L-2*a)+2 ≤ 2*D+F T L+(window T L w).card)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    g+2*(w-D)+2 ≤ (window T (L-2*a) w).card := by
  let l := L-2*a
  let p := L-a
  let m := a-w
  have ep : l+a=p := by dsimp [l,p]; omega
  have eL : p+a=L := by dsimp [p]; omega
  have em : m+w=a := by dsimp [m]; omega
  have ban (x : ℕ) (hx : x∈T) (h : x+a∈T) := sep x hx a ha (x+a) h
  have bad (x : ℕ) (hx : x∈T) : x+a∉T := fun h => by have z := ban x hx h; omega
  have pa := paired T a (l+w) m bad
  have pb := paired T a p w bad
  rw [show l+w+a=p+w by omega] at pa
  rw [eL] at pb
  have whole := partition_len T (l+w) m
  rw [show l+w+m=p by omega] at whole
  have first := partition_len T l w
  have second := partition_len T p w
  have third := partition_len T (p+w) m
  rw [show p+w+m=L by omega] at third
  have cap : (window T L w).card ≤ w := by
    have sb : window T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card sb
  change a+g+2*w+F T l+2≤ 2*D+F T L+(window T L w).card at mass
  change g+2*(w-D)+2≤ (window T l w).card
  omega

theorem twice_gap {T : Finset ℕ} {a L w g D : ℕ} (large : 2*a< L)
    (de : w+D=2*(window T L w).card)
    (mass : g+2*(w-D)+2 ≤ (window T (L-2*a) w).card)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    (∀ t ∈ T,t≤ 2*a → t+g+3*(w-(window T L w).card)+2 ≤ 2*a) ∧
    (∀ t ∈ T,2*a≤ t → 2*a+g+3*(w-(window T L w).card)+2 ≤ t) ∧
    (∀ c ∈ T,∀ d ∈ T,c≤ 2*a → 2*a≤ d → c+w+g+2*(w-(window T L w).card)+2 ≤ d) := by
  let l := L-2*a
  let P := window T l w
  let Q := window T L w
  let H := Ico L (L+w) \ Q
  have eL : l+2*a=L := by dsimp [l]; omega
  have subQ : Q ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
  have cap : Q.card≤ w := by simpa using card_le_card subQ
  have hcard : H.card=w-Q.card := by dsimp [H]; rw [card_sdiff_of_subset subQ]; simp
  have base (t : ℕ) (ht : t∈T) : P.card+Q.card ≤ w+max (2*a-t) (t-2*a) := by
    let X := P.image (t+·)
    let z := min L (l+t)
    let b := max (L+w) (l+t+w)
    have cx : X.card=P.card := card_image_of_injective _ (add_right_injective t)
    have dis : Disjoint X Q := by
      apply disjoint_left.mpr
      intro j hx hq
      obtain ⟨i,hi,e⟩ := mem_image.mp hx
      have bad := sep t ht i (mem_filter.mp hi).1 j (mem_filter.mp hq).1
      change t+i=j at e
      omega
    have inc : X ∪ Q ⊆ Ico z b := by
      intro j hj
      rcases mem_union.mp hj with hx|hq
      · obtain ⟨i,hi,e⟩ := mem_image.mp hx
        obtain ⟨_,lo,up⟩ := mem_filter.mp hi
        change t+i=j at e
        dsimp [z,b]
        exact mem_Ico.mpr ⟨by omega,by omega⟩
      · obtain ⟨_,lo,up⟩ := mem_filter.mp hq
        dsimp [z,b]
        exact mem_Ico.mpr ⟨by omega,by omega⟩
    have room := card_le_card inc
    rw [card_union_of_disjoint dis,cx,Nat.card_Ico] at room
    dsimp [b,z] at room
    omega
  change w+D=2*Q.card at de
  change g+2*(w-D)+2≤ P.card at mass
  refine ⟨?_,?_,?_⟩
  · intro t ht lo
    have b := base t ht
    change t+g+3*(w-Q.card)+2≤ 2*a
    omega
  · intro t ht lo
    have b := base t ht
    change 2*a+g+3*(w-Q.card)+2≤ t
    omega
  · intro c hc d hd cLow dHigh
    let X := H.image (·-c)
    let Y := H.image (·-d)
    let J := Ico (L+w-d) (L-c)
    have inc : P ⊆ (X ∪ Y) ∪ J := by
      intro x hx
      obtain ⟨hit,lo,up⟩ := mem_filter.mp hx
      by_cases left : L≤ x+c
      · apply mem_union_left
        apply mem_union_left
        apply mem_image.mpr
        refine ⟨x+c,mem_sdiff.mpr ⟨mem_Ico.mpr ⟨left,by omega⟩,?_⟩,by omega⟩
        intro h
        have bad := sep x hit c hc (x+c) (mem_filter.mp h).1
        omega
      by_cases right : x+d< L+w
      · apply mem_union_left
        apply mem_union_right
        apply mem_image.mpr
        refine ⟨x+d,mem_sdiff.mpr ⟨mem_Ico.mpr ⟨by omega,right⟩,?_⟩,by omega⟩
        intro h
        have bad := sep x hit d hd (x+d) (mem_filter.mp h).1
        omega
      · exact mem_union_right _ (mem_Ico.mpr ⟨by omega,by omega⟩)
    have outer := (card_le_card inc).trans (card_union_le (X ∪ Y) J)
    have inner := card_union_le X Y
    have cx : X.card≤ H.card := card_image_le
    have cy : Y.card≤ H.card := card_image_le
    have cj : J.card=L-c-(L+w-d) := Nat.card_Ico _ _
    change c+w+g+2*(w-Q.card)+2≤ d
    omega

theorem two_reflections {T : Finset ℕ} {L w U a m c : ℕ} (best : Maximizes T L w U)
    (ha : a ∈ T) (amin : ∀ x ∈ T,a ≤ x) (endpoint : L+w-1 ∈ T) (hc : c ∈ T) (hm : m ∈ T)
    (fits : c+1+w+a ≤ L+w) (apart : m+1+w≤ c+1)
    (gapm : ∀x ∈ T,m< x → m+w< x) (gapc : ∀x ∈ T,c< x → c+w< x)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T,l+1 < i+j ∨ i+j+2 < l) :
    3*F T (L+w-a)+2*(window T L w).card ≤ L+w-2*a+F T (c+1) := by
  have ac := amin c hc
  have two : 2*a ≤ L+w := by omega
  let n := L+w-2*a
  let f (x : ℕ) := L+w-1-x
  let P := window T a n
  let A := P.image f
  have apos : 0 < a := by have h := sep a ha a ha a ha; omega
  have len : a+n=L+w-a := by dsimp [n]; omega
  have bound : L+w ≤ U := best.1
  have Pcard : P = T.filter (· < L+w-a) := by
    ext x
    simp only [P,window,mem_filter,len]
    constructor
    · rintro ⟨xt,_,hi⟩; exact ⟨xt,hi⟩
    · rintro ⟨xt,hi⟩; exact ⟨xt,amin x xt,hi⟩
  have cardA : A.card = P.card := by
    apply card_image_of_injOn
    intro x hx y hy e
    obtain ⟨_,xl,xh⟩ := mem_filter.mp hx
    obtain ⟨_,yl,yh⟩ := mem_filter.mp hy
    dsimp [f] at e
    omega
  have allA : window A a n = A := by
    ext x
    simp only [window,mem_filter,and_iff_left_iff_imp]
    intro hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨_,yl,yh⟩ := mem_filter.mp hy
    dsimp [f]
    exact ⟨by omega,by omega⟩
  have forbidden (h : ℕ) (hm : h ∈ T) (d : ℕ) (diff : h ≤ d ∧ d ≤ h+1) :
      ∀x∈T, x+d ∉ T := by
    intro x hx hit
    have b := sep x hx h hm (x+d) hit
    omega
  have last : ∀ t k, t+k=a+n → disc T t k ≤ 0 := by
    intro t k e
    apply suffix_nonpositive_of_difference best (by omega) (by omega) _ t k e
    apply forbidden a ha
    omega

  have marks (x : ℕ) (mark : 0+x ∈ A) (hU : x ≤ U) :
      x ∉ T ∧ ∀ t k,t+k=x → disc T t k ≤ 0 := by
    rw [Nat.zero_add] at mark
    obtain ⟨y,hy,ex⟩ := mem_image.mp mark
    obtain ⟨yt,yl,yh⟩ := mem_filter.mp hy
    dsimp [f] at ex
    refine ⟨?_,suffix_nonpositive_of_difference best hU (by omega) (forbidden y yt _ (by omega))⟩
    intro xt
    have e := sep x xt y yt (L+w-1) endpoint
    omega
  let e := c+1+w
  let k := e-a
  let r := n-k
  have am := amin m hm
  have ek : a+k=e := by dsimp [e,k]; omega
  have ec : e=c+1+w := rfl
  have endeq : k+r=n := by dsimp [r]; omega
  have er : e+r=a+n := by omega
  have upper := doubled_with_defect marks e r (by omega) 0
    (fun t z hit => last t z (by omega))
  simp only [Nat.zero_add,Nat.add_zero] at upper
  let B := window T L w
  let Z (h : ℕ) := B.image (fun i => L+w+h-i)
  have zcard (h : ℕ) : (Z h).card=B.card := by
    apply card_image_of_injOn
    intro i hi j hj x
    have ui := (mem_filter.mp hi).2.2
    have uj := (mem_filter.mp hj).2.2
    change L+w+h-i=L+w+h-j at x
    omega
  have zrange (h x : ℕ) (hx : x ∈ Z h) : h< x ∧ x≤ h+w := by
    obtain ⟨i,hi,ex⟩ := mem_image.mp hx
    obtain ⟨_,il,iu⟩ := mem_filter.mp hi
    change L+w+h-i=x at ex
    omega
  have za (h : ℕ) (hh : h∈T) (x : ℕ) (hx : x∈Z h) : x∉A := by
    intro ht
    obtain ⟨i,hi,ex⟩ := mem_image.mp hx
    obtain ⟨it,il,iu⟩ := mem_filter.mp hi
    obtain ⟨j,hj,ej⟩ := mem_image.mp ht
    obtain ⟨jt,jl,ju⟩ := mem_filter.mp hj
    change L+w+h-i=x at ex
    dsimp [f] at ej
    have bad := sep j jt h hh i it
    omega
  let V := window T a k
  let W := window A a k
  have vw : Disjoint V W := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨ax,_,xu⟩ := mem_filter.mp hy
    have xm := marks x (by simpa using ax) (by omega)
    exact xm.1 (mem_filter.mp hx).1
  have zsep : Disjoint (Z m) (Z c) := by
    apply disjoint_left.mpr
    intro x hx hy
    have p := zrange m x hx
    have q := zrange c x hy
    omega
  have av (h : ℕ) (hh : h∈T) (blank : ∀x∈T,h< x → h+w< x) :
      Disjoint (Z h) (V ∪ W) := by
    apply disjoint_left.mpr
    intro x hx hother
    rcases mem_union.mp hother with hv|hw
    · obtain ⟨xl,xh⟩ := zrange h x hx
      have impossible := blank x (mem_filter.mp hv).1 xl
      omega
    · exact za h hh x hx (mem_filter.mp hw).1
  have dis : Disjoint (Z m ∪ Z c) (V ∪ W) :=
    Finset.disjoint_union_left.mpr ⟨av m hm gapm,av c hc gapc⟩
  have inc : (Z m ∪ Z c) ∪ (V ∪ W) ⊆ Ico a e := by
    intro x hx
    rcases mem_union.mp hx with h|h
    · rcases mem_union.mp h with h|h
      · have v := zrange m x h
        exact mem_Ico.mpr ⟨by omega,by omega⟩
      · have v := zrange c x h
        exact mem_Ico.mpr ⟨by omega,by omega⟩
    · rcases mem_union.mp h with h|h
      · obtain ⟨_,lo,hi⟩ := mem_filter.mp h
        exact mem_Ico.mpr ⟨lo,by omega⟩
      · obtain ⟨_,lo,hi⟩ := mem_filter.mp h
        exact mem_Ico.mpr ⟨lo,by omega⟩
  have lower := card_le_card inc
  rw [card_union_of_disjoint dis,card_union_of_disjoint zsep,
    card_union_of_disjoint vw,zcard,zcard,Nat.card_Ico] at lower
  have vc : V=T.filter (·< c+1) := by
    ext x
    simp only [V,window,mem_filter]
    constructor
    · rintro ⟨xt,_,hi⟩
      exact ⟨xt,by by_contra! h; have h' := gapc x xt (by omega); omega⟩
    · rintro ⟨xt,hi⟩
      exact ⟨xt,amin x xt,by omega⟩
  have tpart := card_split T a k r
  have apart' := card_split A a k r
  rw [endeq,ek] at tpart apart'
  rw [allA,cardA] at apart'
  change P.card=V.card+(window T e r).card at tpart
  change P.card=W.card+(window A e r).card at apart'
  have pv : F T (L+w-a)=P.card := by rw [Pcard]; rfl
  have cv : F T (c+1)=V.card := by rw [vc]; rfl
  change 3*F T (L+w-a)+2*B.card≤ n+F T (c+1)
  rw [pv,cv]
  omega

theorem paired_growth {T : Finset ℕ} {a : ℕ} (ha : a∈T)
    (sep : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,k+1 < i+j ∨ i+j+2 < k) (p : ℕ) :
    F T (p+2*a) ≤ F T p+a := by
  have b := paired T a p a (fun x hx hit => by have z := sep x hx a ha (x+a) hit; omega)
  have first := partition_len T p a
  have last := partition_len T (p+a) a
  rw [show p+a+a=p+2*a by omega] at last
  omega

theorem empty_between {T : Finset ℕ} {p q : ℕ} (pq : p≤ q)
    (empty : ∀x∈T,p≤ x → q≤ x) : F T p=F T q := by
  unfold F
  congr 1
  ext x
  simp only [mem_filter]
  exact ⟨fun ⟨hit,lo⟩ => ⟨hit,by omega⟩,
    fun ⟨hit,lo⟩ => ⟨hit,by by_contra! h; have bad := empty x hit h; omega⟩⟩

theorem zero_before {T : Finset ℕ} {a : ℕ} (amin : ∀x∈T,a≤ x) : F T a=0 := by
  unfold F
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_lt_of_ge (amin x (mem_filter.mp hx).1)) (mem_filter.mp hx).2

theorem late_point {T : Finset ℕ} {a u L w D c m g : ℕ}
    (_ha : a∈T) (amin : ∀x∈T,a≤ x) (hm : m∈T) (far : L+a< u) (near : u< L+a+w)
    (short : w< a) (cl : c+L< u+a) (ms : m+w+g+2≤ c)
    (hole : ∀ x∈T,m< x → m+w+g+2≤ x)
    (de : w+D=2*(window T L w).card) (dense : a< 2*D)
    (_sep : ∀ i∈T,∀j∈T,∀k∈T,k+1 < i+j ∨ i+j+2 < k)
    (late : 3*F T (L+w+a)+D ≤ L+a+F T (u+a-L))
    (failed : u+a≤ F T u+F T (u+a)+F T (u+2*a)) :
    ∃x∈T,L+w+a≤ x ∧ x< u+a := by
  by_contra! nil
  let p := L+w+a
  let r := u+a-L
  have er : r+L=u+a := by dsimp [r]; omega
  have ep : p=L+w+a := rfl
  have eq := empty_between (T:=T) (p:=p) (q:=u+a) (by omega)
    (fun x hx lo => nil x hx lo)
  have prior := le_prefix T (show u≤ p by omega)
  have tail := growth_upper T (show u+a≤ u+2*a by omega)
  have am := amin m hm
  have he := empty_between (T:=T) (p:=m+1) (q:=m+w+g+2) (by omega)
    (fun x hx lo => hole x hx (by omega))
  have r1 := growth_upper T (show a≤ m+1 by omega)
  have r2 := growth_upper T (show m+w+g+2≤ r by omega)
  rw [zero_before amin] at r1
  have cap : (window T L w).card≤ w := by
    have inc : window T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card inc
  change 3*F T p+D≤ L+a+F T r at late
  omega

theorem before_twice {T : Finset ℕ} {a u L w D g c : ℕ}
    (best : Maximizes T L w (u+2*a)) (ha : a∈T) (hu : u∈T) (amin : ∀x∈T,a≤ x)
    (hL : L∈T) (hR : L+w-1∈T) (large : 2*a< L) (far : L+a< u) (near : u< L+a+w)
    (short : w< a) (wp : 0< w) (de : w+D=2*(window T L w).card) (dense : a< 2*D)
    (width : ∀ t∈T, ∀ v∈T,t+L< u+a → u+a≤ v+L → t+a≤ v)
    (hc : c∈T) (cl : c+L< u+a) (cmax : ∀x∈T,x+L< u+a → x≤ c)
    (cnext : ∀x∈T,c< x → c+a+2< x)
    (wing : a+g+2*w+F T (L-2*a)+2≤ 2*D+F T L+(window T L w).card)
    (sep : ∀ i∈T,∀j∈T,∀k∈T,k+1 < i+j ∨ i+j+2 < k)
    (midDiff : (∃x∈T,L+w+a≤ x ∧ x< u+a) →
      F T (u+a-L)+F T (u+a)+(window T L w).card≤ u+a-L-a+F T (L+w+a))
    (failed : u+a≤ F T u+F T (u+a)+F T (u+2*a)) : c< 2*a := by
  by_contra! cBig
  have packed := twice_wing_mass ha large short de wing sep
  obtain ⟨_,_,cross⟩ := twice_gap large de packed sep
  obtain ⟨m,hm,mlow,mmax,_⟩ := last_prefix ha (show a< 2*a by omega)
  have beyond (x : ℕ) (hx : x∈T) (mx : m< x) : m+w+g+2≤ x := by
    have high : 2*a≤ x := by by_contra! low; have h := mmax x hx low; omega
    have b := cross m hm x hx mlow.le high
    omega
  have ms := beyond c hc (by omega)
  have farRight := near_right ha hu hL hR (amin L hL) short wp width sep (by omega)
  have cL : c< L := by omega
  have cjump := cnext L hL cL
  have lower := two_reflections best ha amin hR hc hm (by omega) (by omega)
    (fun x hx mx => by have h := beyond x hx mx; omega)
    (fun x hx cx => by have h := cnext x hx cx; omega) sep
  let r := u+a-L
  have er : r+L=u+a := by dsimp [r]; omega
  have eq := empty_between (T:=T) (p:=c+1) (q:=r) (by omega) (by
    intro x hx h
    by_contra! low
    have gc := cmax x hx (by omega)
    omega)
  let d := L+w-a
  let p := L+w+a
  have ed : d+a=L+w := by dsimp [d]; omega
  have ep : p=L+w+a := rfl
  have two := paired_growth ha sep d
  rw [show d+2*a=p by omega] at two
  change 3*F T d+2*(window T L w).card≤ L+w-2*a+F T (c+1) at lower
  have late : 3*F T p+D≤ L+a+F T r := by
    clear * - lower eq ed ep two de large er
    omega
  have hit := late_point ha amin hm far near short cl ms beyond de dense sep late failed
  have added := midDiff hit
  change F T r+F T (u+a)+(window T L w).card≤ r-a+F T p at added
  have es := le_prefix T (show u+2*a≤ p+2*a by omega)
  have paired' := paired_growth ha sep p
  have prior :=  le_prefix T (show u≤ p by omega)
  have cap : (window T L w).card≤ w := by
    have inc : window T L w ⊆ Ico L (L+w) := fun _ hx => mem_Ico.mpr (mem_filter.mp hx).2
    simpa using card_le_card inc
  clear * - added late es paired' prior failed dense de cap er far
  omega

theorem mid_difference {T : Finset ℕ} {a u L w : ℕ}
    (far : L+a < u) (near : u < L+w+a) (amin : ∀ t∈T,a ≤ t) (wp : 0 < w)
    (hL : L∈T) (hit : ∃ x∈T,L+w+a ≤ x ∧ x < u+a)
    (sep : ∀ i∈T,∀ j∈T,∀ k∈T,k+1 < i+j ∨ i+j+2 < k) :
    F T (u+a-L)+F T (u+a)+(window T L w).card ≤ u+a-L-a+F T (L+w+a) := by
  obtain ⟨x,xt,xl,xu⟩ := hit
  let X := window T (L+w+a) (u+a-(L+w+a))
  let B := window T L w
  let R := X.image (fun t => t-(L+w))
  let S := B.image (fun t => L+w-1-t)
  let K : Finset ℕ := {0,1}
  have hx (i) (hi : i∈X) : i∈T ∧ L+w+a ≤ i ∧ i < u+a := by
    obtain ⟨it,lo,up⟩ := mem_filter.mp hi
    exact ⟨it,lo,by omega⟩
  have hb (j) (hj : j∈B) : j∈T ∧ L ≤ j ∧ j < L+w := (mem_filter.mp hj)
  have xm : x∈X := mem_filter.mpr ⟨xt,xl,by omega⟩
  have lm : L∈B := mem_filter.mpr ⟨hL,le_rfl,by omega⟩
  have rn : R.Nonempty := ⟨_,mem_image_of_mem _ xm⟩
  have sn : S.Nonempty := ⟨_,mem_image_of_mem _ lm⟩
  have er : R.card=X.card := by
    apply card_image_of_injOn
    intro i hi j hj eq
    change i-(L+w)=j-(L+w) at eq
    obtain ⟨_,il,_⟩ := hx i hi
    obtain ⟨_,jl,_⟩ := hx j hj
    omega
  have es : S.card=B.card := by
    apply card_image_of_injOn
    intro i hi j hj eq
    change L+w-1-i=L+w-1-j at eq
    obtain ⟨_,_,iu⟩ := hb i hi
    obtain ⟨_,_,ju⟩ := hb j hj
    omega
  have cd := cauchy_davenport_add_of_linearOrder_isCancelAdd rn sn
  have cd' := cauchy_davenport_add_of_linearOrder_isCancelAdd (rn.add sn)
    (show K.Nonempty from ⟨0,by simp [K]⟩)
  rw [er,es] at cd
  have kk : K.card=2 := by decide
  rw [kk] at cd'
  have pack := hole_room (T:=T) (S:=(R+S)+K) (show a ≤ u+a-L by omega) (by
    intro t ht
    obtain ⟨rs,hrs,k,hk,et⟩ := mem_add.mp ht
    obtain ⟨r,hr,s,hs,ers⟩ := mem_add.mp hrs
    obtain ⟨i,hi,eir⟩ := mem_image.mp hr
    obtain ⟨j,hj,ejs⟩ := mem_image.mp hs
    change i-(L+w)=r at eir
    change L+w-1-j=s at ejs
    obtain ⟨it,il,ir⟩ := hx i hi
    obtain ⟨jt,jl,jr⟩ := hb j hj
    have kval : k=0 ∨ k=1 := by simpa [K] using hk
    refine ⟨by omega,by omega,?_⟩
    intro tt
    have bad := sep j jt t tt i it
    omega)
  have zero : F T a=0 := by
    have h : T.filter (· < a)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (not_lt_of_ge (amin i (mem_filter.mp hi).1)) (mem_filter.mp hi).2
    simp [F,h]
  rw [zero] at pack
  have part := prefix_partition T (show L+w+a ≤ u+a by omega)
  change F T (u+a)=F T (L+w+a)+X.card at part
  change F T (u+a-L)+F T (u+a)+B.card ≤ u+a-L-a+F T (L+w+a)
  omega

private theorem first_empty {T : Finset ℕ} {a : ℕ} (amin : ∀ x∈T, a≤ x) : F T a=0 := by
  have h : T.filter (·< a)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_lt_of_ge (amin x (mem_filter.mp hx).1)) (mem_filter.mp hx).2
  simp [F,h]

private theorem prefix_on_gap {T : Finset ℕ} {p q : ℕ} (pq : p≤ q)
    (no : ∀ t∈T, t< q → t< p) : F T p=F T q := by
  unfold F
  congr 1
  ext t
  simp only [mem_filter]
  exact ⟨fun ⟨ht,h⟩ => ⟨ht,lt_of_lt_of_le h pq⟩,fun ⟨ht,h⟩ => ⟨ht,no t ht h⟩⟩

private theorem final_difference {T : Finset ℕ} {a u z v h : ℕ} (uz : u≤ z)
    (zT : z∈T) (vT : v∈T) (gap : z+a+2< v) (vh : v≤ h)
    (equal : F T (z+1)=F T v) (amin : ∀ x∈T,a≤ x)
    (sep : ∀ i∈T,∀ j∈T,∀ k∈T,k+1 < i+j ∨ i+j+2 < k) :
    F T h + F T (h-u) ≤ (h-u-a) + F T u := by
  let X := window T v (h+1-v)
  let Y := window T u (z+1-u)
  let R := X.image (fun t => t-(z+2))
  let S := Y.image (fun t => z-t)
  let K : Finset ℕ := {0,1}
  have hx (t) (ht : t∈X) : t∈T ∧ v≤ t ∧ t≤ h := by
    obtain ⟨hit,lo,hi⟩ := mem_filter.mp ht
    exact ⟨hit,lo,by omega⟩
  have hy (t) (ht : t∈Y) : t∈T ∧ u≤ t ∧ t≤ z := by
    obtain ⟨hit,lo,hi⟩ := mem_filter.mp ht
    exact ⟨hit,lo,by omega⟩
  have rv : v∈X := mem_filter.mpr ⟨vT,le_rfl,by omega⟩
  have sz : z∈Y := mem_filter.mpr ⟨zT,uz,by omega⟩
  have rn : R.Nonempty := ⟨_, mem_image_of_mem _ rv⟩
  have sn : S.Nonempty := ⟨_, mem_image_of_mem _ sz⟩
  have er : R.card=X.card := by
    apply card_image_of_injOn
    intro i hi j hj eq
    change i-(z+2)=j-(z+2) at eq
    obtain ⟨_,li,_⟩ := hx i hi
    obtain ⟨_,lj,_⟩ := hx j hj
    omega
  have es : S.card=Y.card := by
    apply card_image_of_injOn
    intro i hi j hj eq
    change z-i=z-j at eq
    obtain ⟨_,_,li⟩ := hy i hi
    obtain ⟨_,_,lj⟩ := hy j hj
    omega
  have cd := cauchy_davenport_add_of_linearOrder_isCancelAdd rn sn
  have cd' := cauchy_davenport_add_of_linearOrder_isCancelAdd (rn.add sn)
    (show K.Nonempty from ⟨0,by simp [K]⟩)
  rw [er,es] at cd
  have kk : K.card=2 := by decide
  rw [kk] at cd'
  have pack := hole_room (T:=T) (S:=(R+S)+K) (show a≤ h-u by omega) (by
    intro t ht
    obtain ⟨rs,hrs,k,hk,et⟩ := mem_add.mp ht
    obtain ⟨r,hr,s,hs,ers⟩ := mem_add.mp hrs
    obtain ⟨i,hi,eir⟩ := mem_image.mp hr
    obtain ⟨j,hj,ejs⟩ := mem_image.mp hs
    change i-(z+2)=r at eir
    change z-j=s at ejs
    obtain ⟨it,il,ir⟩ := hx i hi
    obtain ⟨jt,jl,jr⟩ := hy j hj
    have kval : k=0 ∨ k=1 := by simpa [K] using hk
    refine ⟨by omega,by omega,?_⟩
    intro tt
    have bad := sep j jt t tt i it
    omega)
  have x := prefix_partition T (show v≤ h+1 by omega)
  have y := prefix_partition T (show u≤ z+1 by omega)
  change F T (h+1)=F T v+X.card at x
  change F T (z+1)=F T u+Y.card at y
  have mon := le_prefix T (show h≤ h+1 by omega)
  rw [first_empty amin] at pack
  omega

private theorem final_third {T : Finset ℕ} {a u L w D c v z v' : ℕ}
    (_hL : L∈T) (hv : v∈T) (wp : 0< w) (short : w< a) (far : L+a< u)
    (de : w+D=2*(window T L w).card) (gap : c+a+2< v)
    (uz : u≤ z) (zp : z+a< c+(L+w))
    (vlow : u+a≤ L+v) (vhigh : v≤ u+2*a-L) (bad : L+v< v')
    (next : ∀x∈T,u+a≤ x → v'≤ x)
    (mass : F T u+2*F T (u+a)≤ u+D)
    (failed : u+a≤ F T u+F T (u+a)+F T (u+2*a))
    (sep : ∀ i∈T,∀ j∈T,∀ k∈T,k+1 < i+j ∨ i+j+2 < k) : False := by
  let n := u+2*a-L-v
  have endEq : v+L+n=u+2*a := by dsimp [n]; omega
  have nw : n< w := by dsimp [n]; omega
  let P := window T L n
  have cap := shifted_room (P:=P) (show v+L≤ u+2*a by omega) hv sep (by
    intro t ht
    obtain ⟨tt,tl,tu⟩ := mem_filter.mp ht
    exact ⟨tt,by omega,by omega⟩)
  have same := prefix_on_gap (T:=T) (p:=u+a) (q:=v+L) (by omega) (by
    intro t tt lo
    by_contra! hi
    have h := next t tt hi
    omega)
  have s := card_split T L n (w-n)
  rw [show n+(w-n)=w by omega] at s
  have inc : window T (L+n) (w-n) ⊆ Ico (L+n) (L+n+(w-n)) :=
    fun _ h => mem_Ico.mpr (mem_filter.mp h).2
  have le := card_le_card inc
  rw [Nat.card_Ico] at le
  change P.card+F T (u+2*a)≤ u+2*a-(v+L)+F T (v+L) at cap
  change (window T L w).card=P.card+(window T (L+n) (w-n)).card at s
  have whole : (window T L w).card ≤ w := by
    have ins : window T L w ⊆ Ico L (L+w) := fun _ h => mem_Ico.mpr (mem_filter.mp h).2
    simpa using card_le_card ins
  omega

private theorem next_cell {T : Finset ℕ} {j s : ℕ} (hs : s∈T) (js : j< s) :
    ∃ v∈T, j< v ∧ v≤ s ∧ (∀ x∈T,j< x → v≤ x) ∧ F T (j+1)=F T v := by
  let P := T.filter (j<·)
  have non : P.Nonempty := ⟨s,mem_filter.mpr ⟨hs,js⟩⟩
  let v := P.min' non
  obtain ⟨vt,after⟩ := mem_filter.mp (min'_mem P non)
  have first (x) (xt : x∈T) (later : j< x) : v≤ x := min'_le P x (mem_filter.mpr ⟨xt,later⟩)
  refine ⟨v,vt,after,first s hs js,first,prefix_on_gap (by omega) ?_⟩
  intro t tt lo
  by_contra! beyond
  have vlow := first t tt (by omega)
  omega

theorem final_fgy {T : Finset ℕ} {a u L w D c z m : ℕ}
    (best : Maximizes T L w (u+2*a)) (ha : a∈T) (hu : u∈T) (hs : u+2*a∈T)
    (amin : ∀x∈T,a≤ x) (hL : L∈T) (large : 2*a< L) (far : L+a< u) (wp : 0< w) (short : w< a)
    (de : w+D=2*(window T L w).card) (mass : F T u+2*F T (u+a)≤ u+D)
    (csmall : c< 2*a) (hc : c∈T) (clow : c+L< u+a)
    (cmax : ∀x∈T,x+L< u+a → x≤ c) (cnext : ∀x∈T,c< x → c+a+2< x)
    (hz : z∈T) (uz : u≤ z) (zx : z< u+a) (zwing : z+a< c+(L+w))
    (zmax : ∀x∈T,x< u+a → x≤ z) (znext : ∀x∈T,z< x → z+a+2< x)
    (hm : m∈T) (ml : L-2*a≤ m) (mr : m< L-a)
    (wing : F T L+F T (L-m)≤ a+F T (L-2*a))
    (dif : ∀p q : ℕ,p≤q → q≤u+2*a → 2*F T q+F T (q-p) ≤ q-p+D+2*F T p)
    (sep : ∀ i∈T,∀ j∈T,∀ k∈T,k+1 < i+j ∨ i+j+2 < k) :
    F T u+F T (u+a)+F T (u+2*a)< u+a := by
  by_contra! failed
  let y := u+2*a-L
  have ey : y+L=u+2*a := by dsimp [y]; omega
  have y3 : 3*a< y := by omega
  obtain ⟨v,hv,cv,vhigh,vmin,veq⟩ := next_cell (j:=c) hs (by omega)
  obtain ⟨v',hv',zv',v'high,v'min,v'eq⟩ := next_cell (j:=z) hs (by omega)
  have cvgap := cnext v hv cv
  have zvgap := znext v' hv' zv'
  have vlow : u+a≤ L+v := by by_contra! no; have h := cmax v hv (by omega); omega
  have v'low : u+a≤ v' := by by_contra! no; have h := zmax v' hv' no; omega
  have ev := prefix_on_gap (T:=T) (p:=c+1) (q:=2*a) (by omega) (by
    intro t tt ht
    have b := cmax t tt (by omega)
    omega)
  have fv : F T v=F T (2*a) := veq.symm.trans ev
  have diff := dif y u (by omega) (by omega)
  rw [show u-y=L-2*a by omega] at diff
  have ten : F T u+F T (L-2*a)+F T (u+2*a)+3*a ≤ u+a+D+F T (2*a) := by
    by_cases terminal : y< v
    · have fy := prefix_on_gap (T:=T) (p:=c+1) (q:=y) (by omega) (by
        intro t tt ht
        by_contra! beyond
        have b := vmin t tt (by omega)
        omega)
      have d := final_difference uz hz hv' zvgap v'high v'eq amin sep
      rw [show u+2*a-u=2*a by omega] at d
      omega
    · have vy : v≤ y := by omega
      by_cases overlap : v'≤ L+v
      · let q := L+v-u
        have eq : q+u=L+v := by dsimp [q]; omega
        have d := final_difference uz hz hv' zvgap overlap v'eq amin sep
        change F T (L+v)+F T q≤ q-a+F T u at d
        have anch := anchored_window best hL sep vy (show y≤ u+2*a by omega) (show L+y∈T by rwa [show L+y=u+2*a by omega])
        rw [show L+y=u+2*a by omega,fv] at anch
        have grow : F T (2*a)≤ F T q+(y-3*a) := by
          by_cases hq : q≤ c+1
          · have h := growth_upper T hq
            omega
          · have h := le_prefix T (show c+1≤ q by omega)
            omega
        omega
      · exact False.elim (final_third hL hv wp short far de cvgap uz zwing vlow vy (by omega)
          (fun x xt xhi => v'min x xt (by omega)) mass failed sep)
  let P := window T (L-m) (2*a-(L-m))
  have pp := prefix_partition T (show L-m≤ 2*a by omega)
  change F T (2*a)=F T (L-m)+P.card at pp
  have shift := shifted_room (P:=P) (show L≤ L+a by omega) hm sep (by
    intro t ht
    obtain ⟨tt,lo,hi⟩ := mem_filter.mp ht
    exact ⟨tt,by omega,by omega⟩)
  have trans := shifted_room (P:=window T L w) (show L+a≤ L+w+a by omega) ha sep (by
    intro t ht
    obtain ⟨tt,lo,hi⟩ := mem_filter.mp ht
    exact ⟨tt,by omega,by omega⟩)
  have same := prefix_on_gap (T:=T) (p:=L+w+a) (q:=u+a) (by omega) (by
    intro t tt ht
    have h := zmax t tt ht
    omega)
  have cap : (window T L w).card≤ w := by
    have ins : window T L w ⊆ Ico L (L+w) := fun _ h => mem_Ico.mpr (mem_filter.mp h).2
    simpa using card_le_card ins
  omega

end GreenFinalLocal

open GreenFinalLocal

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1_H3_R1.H3 := by
  intro T a u L w D ha hu hs amin high _lu inside hL hR short wp best eq mass _gap width sep dif g c z cfg
  obtain ⟨far,near,dense,hc,cl,cmax,cnext,hz,uz,zx,zwing,zmax,znext,_,_,wing⟩ := cfg
  have mx : Maximizes T L w (u+2*a) := ⟨by omega,by
    intro p n hi
    have b := best p n hi
    unfold disc window
    omega⟩
  by_contra! failed
  have small := before_twice mx ha hu amin hL hR high far near short wp eq dense width hc cl cmax cnext wing sep
    (fun hit => mid_difference far (by omega) amin wp hL hit sep) failed
  obtain ⟨m,hm,ml,mr,_,mw⟩ := wing_witness ha hL amin high short eq sep wing
  exact (not_lt_of_ge failed) (final_fgy mx ha hu hs amin hL high far wp short eq mass small hc cl cmax cnext
    hz uz zx zwing zmax znext hm ml mr mw dif sep)

end GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H3

namespace GreenAssembly.GR1H2R1H2R1H3

/- Three deadline families and the generating polynomial. Original Lean proof by @Deldor14.
The three-prefix inequality is from Franchi–Gowers–Yip, arXiv:2607.06073, Lemma 2.1. -/

open Finset

private lemma matching_of_prefix {ι : Type} [Fintype ι] (w : ι → ℕ)
    (h : ∀ n : ℕ, (univ.filter (fun z => w z<n)).card ≤ n) :
    ∃ f : ι → ℕ, Function.Injective f ∧ ∀ z, f z ≤ w z := by
  classical
  obtain ⟨f,hf,hw⟩ := (all_card_le_biUnion_card_iff_exists_injective (fun z => range (w z+1))).mp (by
    intro s
    by_cases hne : s.Nonempty
    · obtain ⟨z,hz,hmax⟩ := s.exists_max_image w hne
      have hs : s ⊆ univ.filter (fun i => w i < w z+1) := by
        intro i hi
        exact mem_filter.mpr ⟨mem_univ _,Nat.lt_succ_of_le (hmax i hi)⟩
      have hb : range (w z+1) ⊆ s.biUnion (fun i => range (w i+1)) :=
        fun _ hi => mem_biUnion.mpr ⟨z,hz,hi⟩
      have hcard := card_le_card hb
      rw [card_range] at hcard
      exact (card_le_card hs).trans ((h _).trans hcard)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne])
  exact ⟨f,hf,fun z => Nat.le_of_lt_succ (mem_range.mp (hw z))⟩

private lemma shifted_matching (T : Finset ℕ) (a : ℕ) (ha : ∀ i ∈ T, a ≤ i)
    (hcum : ∀ n : ℕ, (T.filter (·<n-a)).card + (T.filter (·<n)).card +
        (T.filter (·<n+a)).card ≤ n) :
    ∃ f : T ⊕ (T ⊕ T) → ℕ, Function.Injective f ∧
      ∀ z : T, f (.inl z) ≤ z.val+a ∧ f (.inr (.inl z)) ≤ z.val ∧ f (.inr (.inr z)) ≤ z.val-a := by
  classical
  let w : T ⊕ (T ⊕ T) → ℕ := Sum.elim (fun z => z.val+a)
      (Sum.elim (fun z => z.val) (fun z => z.val-a))
  have hp (n : ℕ) : (univ.filter (fun z => w z<n)).card ≤ n := by
    have hc (g : ℕ → Prop) [DecidablePred g] :
        (∑ z : T, if g z.val then 1 else 0) = (T.filter g).card := by
      change (∑ z ∈ T.attach, if g z.val then 1 else 0) = _
      rw [Finset.sum_attach T (fun z => if g z then 1 else 0),Finset.card_filter]
    have hswap (z : T) : z.val+a < n ↔ z.val < n-a := by omega
    have hsub (z : T) : z.val-a < n ↔ z.val < n+a := by have := ha z.val z.property; omega
    rw [Finset.card_filter]
    simp only [Fintype.sum_sum_type, w, Sum.elim_inl, Sum.elim_inr, hswap, hsub]
    change (∑ z : T, if z.val < n-a then 1 else 0) + ((∑ z : T, if z.val < n then 1 else 0) + (∑ z : T, if z.val < n+a then 1 else 0)) ≤ n
    rw [hc (fun i => i<n-a), hc (fun i => i<n), hc (fun i => i<n+a)]
    simpa [add_assoc] using hcum n
  obtain ⟨f,hf,hw⟩ := matching_of_prefix w hp
  exact ⟨f,hf,fun z => ⟨hw (.inl z),hw (.inr (.inl z)),hw (.inr (.inr z))⟩⟩

private lemma matched_sum {ι : Type} [Fintype ι] (f : ι → ℕ) (hf : Function.Injective f)
    (q : ℝ) (hq : 0<q) (hq1 : q<1) : (1-q)*(∑ z, q^(f z)) ≤ 1 := by
  classical
  let A := univ.image f
  obtain ⟨n,hn⟩ := A.exists_nat_subset_range
  have hs : (∑ z, q^(f z)) = ∑ i ∈ A, q^i := by
    dsimp [A]
    rw [sum_image (fun _ _ _ _ he => hf he)]
  have hbound : (∑ i ∈ A, q^i) ≤ ∑ i ∈ range n, q^i :=
    sum_le_sum_of_subset_of_nonneg hn (fun _ _ _ => by positivity)
  have hgeom := geom_sum_mul_neg q n
  have hqN : 0 ≤ q^n := by positivity
  rw [hs]
  nlinarith only [mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hq1.le),hgeom,hqN]

private lemma weighted_bound (T : Finset ℕ) (a : ℕ) (ha : ∀ j ∈ T, a ≤ j)
    (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (f : T ⊕ (T ⊕ T) → ℕ) (hf : Function.Injective f)
    (hw : ∀ z : T, f (.inl z) ≤ z.val+a ∧ f (.inr (.inl z)) ≤ z.val ∧
      f (.inr (.inr z)) ≤ z.val-a) :
    (1-q)*(∑ j ∈ T, q^j) ≤ 1/3 := by
  let w : T ⊕ (T ⊕ T) → ℕ := Sum.elim (fun z => z.val+a)
    (Sum.elim (fun z => z.val) (fun z => z.val-a))
  have hpoint (z) : f z ≤ w z := by
    rcases z with z | z | z
    · exact (hw z).1
    · exact (hw z).2.1
    · exact (hw z).2.2
  have hs := Finset.sum_le_sum (s:=univ) (fun z _ =>
    pow_le_pow_of_le_one hq.le hq1.le (hpoint z))
  have hsel := (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hq1.le)).trans (matched_sum f hf q hq hq1)
  have hqa : 0 < q^a := by positivity
  have hsub (z : T) : q^(z.val-a) = q^z.val * (q^a)⁻¹ := by
    rw [← div_eq_mul_inv,eq_div_iff hqa.ne',←pow_add,Nat.sub_add_cancel (ha z.val z.property)]
  have hTs : (∑ z : T, q^z.val) = ∑ j ∈ T, q^j := Finset.sum_attach T (fun j => q^j)
  have he : (∑ z, q^(w z)) = (q^a+1+(q^a)⁻¹)*(∑ j ∈ T, q^j) := by
    simp only [Fintype.sum_sum_type,w,Sum.elim_inl,Sum.elim_inr,pow_add,hsub,←sum_mul,hTs]
    ring
  rw [he] at hsel
  have hcoef : 3 ≤ q^a+1+(q^a)⁻¹ := by
    apply (le_of_mul_le_mul_right _ hqa)
    nlinarith only [sq_nonneg (q^a-1),inv_mul_cancel₀ hqa.ne']
  have hprod : 0 ≤ (1-q)*(∑ i ∈ T, q^i) := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hcoef hprod,hsel]

theorem result : OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H3 := by
  intro T a hmin hcum q hq hq1
  obtain ⟨f,hf,hw⟩ := shifted_matching T a hmin hcum
  exact weighted_bound T a hmin q hq hq1 f hf hw

end GreenAssembly.GR1H2R1H2R1H3

theorem OMA.solution : type_of% @Green3.green_3 :=
  (OMA.R_Green3_green_3_R1.main GreenAssembly.GR1H1.result (OMA.R_Green3_green_3_R1_H2_R1.main GreenAssembly.GR1H2R1H1.result (OMA.R_Green3_green_3_R1_H2_R1_H2_R1.main GreenAssembly.GR1H2R1H2R1H1.result (OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1.main GreenAssembly.GR1H2R1H2R1H2R1H1.result (OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1.main GreenAssembly.GR1H2R1H2R1H2R1H2R1H1.result (OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.main GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H1.result GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H2.result (OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1.main GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H1.result GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H2.result (OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1.main GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H1.result (OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1.main GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H1.result GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H2.result (OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H3_R1_H3_R1_H2_R1_H3_R1.main GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H1.result GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H2.result GreenAssembly.GR1H2R1H2R1H2R1H2R1H2R1H3R1H3R1H2R1H3R1H3.result))))))) GreenAssembly.GR1H2R1H2R1H3.result)))
