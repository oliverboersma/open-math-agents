import FormalConjectures.ErdosProblems.«103»
import Mathlib

/-! A point strictly inside both distance constraints can be moved, producing
a noncongruent diameter minimizer. -/

open EuclideanGeometry Filter Finset
open Erdos103
open scoped Classical ENNReal

namespace OMA.R_Erdos103_erdos_103_variants_two_le_R1

/-- Existence of diameter minimizers. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ A : Finset ℝ², IsMinimiser n A

/-- The remaining configurations have every point involved in a tight
unit-distance or diameter constraint, in every minimizer. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (∃ A : Finset ℝ², IsMinimiser n A) →
    (∀ A : Finset ℝ², IsMinimiser n A → ∀ p ∈ A,
      ∃ q ∈ A.erase p, dist p q = 1 ∨ dist p q = Metric.diam (A : Set ℝ²)) →
    ∃ A B : Finset ℝ², IsMinimiser n A ∧ IsMinimiser n B ∧ ¬ Congruent A B

section Proof

private theorem congruent_symm {A B : Finset ℝ²} (h : Congruent A B) : Congruent B A := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,?_⟩
  rw [← he,Set.image_image]
  simp

theorem two_classes_of_pair {n : ℕ} {A B : Finset ℝ²} (hA : IsMinimiser n A)
    (hB : IsMinimiser n B) (hc : ¬ Congruent A B) : 2 ≤ Erdos103.h n := by
  have hne : A ≠ B := by
    intro h
    subst B
    apply hc
    refine ⟨IsometryEquiv.refl _,?_⟩
    change id '' (A : Set ℝ²) = A
    exact Set.image_id _
  let S : Finset (Finset ℝ²) := {A,B}
  have hBoth : (∀ X ∈ S, IsMinimiser n X) ∧
      ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → ¬ Congruent X Y := by
    constructor
    · intro X hX
      rcases (show X=A ∨ X=B from by simpa [S] using hX) with rfl|rfl
      · exact hA
      · exact hB
    · intro X hX Y hY hXY
      have hX' : X=A ∨ X=B := by simpa [S] using hX
      have hY' : Y=A ∨ Y=B := by simpa [S] using hY
      rcases hX' with hx|hx <;> rcases hY' with hy|hy <;> subst X <;> subst Y
      · exact (hXY rfl).elim
      · exact hc
      · exact fun hh => hc (congruent_symm hh)
      · exact (hXY rfl).elim
  have hcard : (S.card:ℕ∞) = 2 := by simp [S,Finset.card_pair hne]
  rw [← hcard]
  exact le_iSup_of_le S (le_iSup_of_le hBoth le_rfl)

theorem exists_moved_minimizer {n : ℕ} {A : Finset ℝ²} (hA : IsMinimiser n A)
    (hn : 2 ≤ n) {p : ℝ²} (hp : p ∈ A)
    (hFree : ∀ q ∈ A.erase p, 1 < dist p q ∧ dist p q < Metric.diam (A : Set ℝ²)) :
    ∃ B, IsMinimiser n B ∧ ¬ Congruent A B := by
  let C := A.erase p
  let D := Metric.diam (A : Set ℝ²)
  have hAcard : A.card = n := hA.1.1
  have hCcard : C.card = n-1 := by rw [card_erase_of_mem hp,hAcard]
  have hC : C.Nonempty := card_pos.mp (by omega)
  have hCcopy := hC
  obtain ⟨q,hq⟩ := hCcopy
  let d := dist p q
  have hd : 0 < d := (by norm_num : (0:ℝ)<1).trans (hFree q hq).1
  let margin (u : ℝ²) := min (dist p u - 1) (D-dist p u)
  let δ := C.inf' hC margin
  have hδ : 0 < δ := by
    obtain ⟨x,hx,hEq⟩ := exists_mem_eq_inf' hC margin
    have hh := hFree x hx
    change 0 < C.inf' hC margin
    rw [hEq]
    exact lt_min (by linarith [hh.1]) (by linarith [hh.2])
  have hMargin (u : ℝ²) (hu : u ∈ C) : δ ≤ margin u := inf'_le margin hu
  let DS := (A ×ˢ A).image fun xy => dist xy.1 xy.2
  have hInf : (Set.Ioo d (d+δ)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨r,hr⟩ := (hInf.sdiff DS.finite_toSet).nonempty
  have hrLo : d < r := hr.1.1
  have hrHi : r < d+δ := hr.1.2
  have hrD : r ∉ DS := hr.2
  let z := q + (r/d) • (p-q)
  have hNorm : ‖p-q‖ = d := (dist_eq_norm _ _).symm
  have hzq : dist z q = r := by
    rw [dist_eq_norm]
    change ‖q + (r/d) • (p-q)-q‖ = r
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (div_nonneg (hd.trans hrLo).le hd.le),hNorm]
    exact div_mul_cancel₀ _ hd.ne'
  have hzp : dist z p < δ := by
    rw [dist_eq_norm]
    have hEq : z-p = (r/d-1) • (p-q) := by
      dsimp [z]
      rw [sub_smul,one_smul]
      abel
    rw [hEq,norm_smul,Real.norm_of_nonneg (by
      have hh : 1 ≤ r/d := (le_div_iff₀ hd).mpr (by simpa using hrLo.le)
      linarith),hNorm,sub_mul,div_mul_cancel₀ _ hd.ne',one_mul]
    linarith
  have hDistances (u : ℝ²) (hu : u ∈ C) : 1 < dist z u ∧ dist z u < D := by
    have h0 := hMargin u hu
    have h1 := h0.trans (min_le_left _ _)
    have h2 := h0.trans (min_le_right _ _)
    have h3 := dist_triangle p z u
    have h4 := dist_triangle z p u
    rw [dist_comm p z] at h3
    constructor <;> linarith
  have hzC : z ∉ C := by
    intro h
    have hh := (hDistances z h).1
    simp only [dist_self] at hh
    linarith
  let B := insert z C
  have hBcard : B.card = n := by rw [card_insert_of_notMem hzC,hCcard]; omega
  have hOld (u : ℝ²) (hu : u ∈ C) : u ∈ A := mem_of_mem_erase hu
  have hSep : B ∈ separatedSets n := by
    refine ⟨hBcard,?_⟩
    intro x hx y hy hxy
    change (1:ℝ≥0∞) ≤ edist x y
    change x ∈ B at hx
    change y ∈ B at hy
    have hBxy : 1 ≤ dist x y := by
      rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with rfl|hy
      · exact (hxy rfl).elim
      · exact (hDistances y hy).1.le
      · simpa [dist_comm] using (hDistances x hx).1.le
      · have hh := hA.1.2 (hOld x hx) (hOld y hy) hxy
        change (1:ℝ≥0∞) ≤ edist x y at hh
        rw [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hh
        exact hh
    rw [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg]
    exact hBxy
  have hDiam : Metric.diam (B : Set ℝ²) ≤ D := by
    apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
    intro x hx y hy
    change x ∈ B at hx
    change y ∈ B at hy
    rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with rfl|hy
    · simp [Metric.diam_nonneg]
    · exact (hDistances y hy).2.le
    · simpa [dist_comm] using (hDistances x hx).2.le
    · exact Metric.dist_le_diam_of_mem A.finite_toSet.isBounded (hOld x hx) (hOld y hy)
  refine ⟨B,⟨hSep,?_⟩,?_⟩
  · intro X hX
    exact hDiam.trans (hA.2 hX)
  · rintro ⟨e,he⟩
    have hzB : z ∈ (B : Set ℝ²) := mem_insert_self _ _
    have hqB : q ∈ (B : Set ℝ²) := mem_insert_of_mem hq
    have hzImage : z ∈ e '' (A : Set ℝ²) := by rw [he]; exact hzB
    have hqImage : q ∈ e '' (A : Set ℝ²) := by rw [he]; exact hqB
    obtain ⟨u,hu,huZ⟩ := hzImage
    obtain ⟨v,hv,hvQ⟩ := hqImage
    apply hrD
    refine mem_image.mpr ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,?_⟩
    calc
      dist u v = dist (e u) (e v) := (e.isometry.dist_eq u v).symm
      _ = r := by rw [huZ,hvQ,hzq]

theorem main : H1 → H2 → type_of% @Erdos103.erdos_103.variants.two_le := by
  intro hExist hBoundary
  filter_upwards [hExist,hBoundary,(eventually_ge_atTop 2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n)] with n hn hBound hn2
  by_cases hTight : ∀ A : Finset ℝ², IsMinimiser n A → ∀ p ∈ A,
      ∃ q ∈ A.erase p, dist p q = 1 ∨ dist p q = Metric.diam (A : Set ℝ²)
  · obtain ⟨A,B,hA,hB,hN⟩ := hBound hn hTight
    exact two_classes_of_pair hA hB hN
  push Not at hTight
  obtain ⟨A,hA,p,hp,hFree⟩ := hTight
  have hDistance (q : ℝ²) (hq : q ∈ A.erase p) :
      1 < dist p q ∧ dist p q < Metric.diam (A : Set ℝ²) := by
    have hqA := (mem_erase.mp hq).2
    have hne := (mem_erase.mp hq).1
    have hLow := hA.1.2 hp hqA hne.symm
    change (1:ℝ≥0∞) ≤ edist p q at hLow
    rw [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hLow
    have hHigh := Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hp hqA
    exact ⟨lt_of_le_of_ne hLow (hFree q hq).1.symm,lt_of_le_of_ne hHigh (hFree q hq).2⟩
  obtain ⟨B,hB,hNo⟩ := exists_moved_minimizer hA hn2 hp hDistance
  exact two_classes_of_pair hA hB hNo

end Proof

end OMA.R_Erdos103_erdos_103_variants_two_le_R1
