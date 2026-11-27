import FormalConjectures.GreensOpenProblems.«54»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Green54_green_54_known_case_R1
open Set MeasureTheory ProbabilityTheory Green54
open scoped Pointwise ENNReal

theorem cylinder_measure (I : Finset ℕ) (A : Set (I → ℝ)) (hA : MeasurableSet A) :
    gaussianMeasureInf (I.restrict ⁻¹' A) = (Measure.pi fun _ : I ↦ gaussianReal 0 1) A := by
  rw [← Measure.map_apply I.continuous_restrict.measurable hA]
  rw [gaussianMeasureInf, Measure.infinitePi_map_restrict]

/-- Talagrand's finite-dimensional two-summand obstruction. -/
def H1 : Prop := ∃ (I : Finset ℕ) (A : Set (I → ℝ)), MeasurableSet A ∧ Balanced ℝ A ∧
  (0.99 : ℝ≥0∞) < (Measure.pi fun _ : I ↦ gaussianReal 0 1) A ∧
  ∀ C : Set (I → ℝ), IsCompact C → Convex ℝ C → C ⊆ A + A →
    (Measure.pi fun _ : I ↦ gaussianReal 0 1) C < (0.01 : ℝ≥0∞)

/-- Inner approximation of a balanced Gaussian cylinder by compact balanced sets. -/
def H2 : Prop := ∀ (I : Finset ℕ) (A : Set (I → ℝ)) (r : ℝ≥0∞),
  MeasurableSet A → Balanced ℝ A → r < (Measure.pi fun _ : I ↦ gaussianReal 0 1) A →
  ∃ K : Set (ℕ → ℝ), IsCompact K ∧ Balanced ℝ K ∧ r ≤ gaussianMeasureInf K ∧
    K ⊆ I.restrict ⁻¹' A

theorem main : H1 → H2 → type_of% @Green54.green_54_known_case := by
  rintro ⟨I,A,hm,hb,hr,small⟩ lift all
  obtain ⟨K,hK,hKb,hKm,hKA⟩ := lift I A _ hm hb hr
  obtain ⟨C,hC,hCv,hsub,hmass⟩ := all K hK hKb hKm
  let D := I.restrict '' C
  have hD : IsCompact D := hC.image I.continuous_restrict
  have hcv : Convex ℝ D := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ a b ha hb hab
    exact ⟨_, hCv hx hy ha hb hab, rfl⟩
  have hDA : D ⊆ A + A := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨u,hu,v,hv,rfl⟩ := hsub hx
    exact ⟨_,hKA hu,_,hKA hv,rfl⟩
  apply (small D hD hcv hDA).not_ge
  rw [← cylinder_measure I D hD.measurableSet]
  exact hmass.trans (measure_mono (Set.subset_preimage_image _ _))

end OMA.R_Green54_green_54_known_case_R1
