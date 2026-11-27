import OMAReductions.R_Erdos604_erdos_604_variants_average_R2_H2_R1

/-!
# Circle incidences from a crossing lemma and cyclic arc extraction

Reduction by Hanan Beer (@hananzlt), following the circle-incidence construction
of László A. Székely, Crossing Numbers and Hard Erdős Problems in Discrete
Geometry (1997). The two inputs separate the crossing inequality for simple
circular-arc drawings from the cyclic ordering and thinning of circle arcs.
The related formal geometric drawing development is due to Wesley Pegden and
Trellis; the arithmetic uses the crossing-number organization of @JaviSoto.
-/

namespace OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1_H1_R1

open Finset
open scoped EuclideanGeometry Classical

/-- The crossing lemma for simple graphs drawn by injective circular arcs.
The intersection count includes adjacent-edge intersections and tangencies. -/
def H1 : Prop :=
  ∃ K : ℕ, 0 < K ∧ ∀ (A : Finset ℝ²) (E : Finset ℕ)
    (γ : ℕ → C(unitInterval, ℝ²)),
    (∀ i ∈ E, Function.Injective (γ i) ∧ γ i 0 ∈ A ∧ γ i 1 ∈ A ∧
      (∀ t, 0 < t → t < 1 → γ i t ∉ A) ∧
      ∃ c : ℝ², ∃ r : ℝ, 0 < r ∧ ∀ t, dist (γ i t) c = r) →
    Set.InjOn (fun i => ({γ i 0, γ i 1} : Finset ℝ²)) (E : Set ℕ) →
    (∀ i ∈ E, ∀ j ∈ E, i ≠ j →
      ((Set.range (γ i) ∩ Set.range (γ j)) \ (A : Set ℝ²)).Finite) →
    let X := ∑ i ∈ E, ∑ j ∈ E.erase i,
      ((Set.range (γ i) ∩ Set.range (γ j)) \ (A : Set ℝ²)).ncard
    E.card ≤ K * A.card ∨ E.card ^ 3 ≤ K * A.card ^ 2 * X

/-- Cyclic arcs on the circles, thinned to one arc per unordered endpoint pair.
Discarding circles with at most two points costs at most twice their number. -/
def H2 : Prop :=
  ∀ (A : Finset ℝ²) (L : Finset (ℝ² × ℝ)),
    (∀ c ∈ L, 0 < c.2) →
    (∀ y ∈ A, ∀ z ∈ A, y ≠ z →
      (L.filter fun c => dist y c.1 = c.2 ∧ dist z c.1 = c.2).card ≤ 2) →
    ∃ E : Finset ℕ, ∃ γ : ℕ → C(unitInterval, ℝ²),
      (∀ i ∈ E, Function.Injective (γ i) ∧ γ i 0 ∈ A ∧ γ i 1 ∈ A ∧
        (∀ t, 0 < t → t < 1 → γ i t ∉ A) ∧
        ∃ c : ℝ², ∃ r : ℝ, 0 < r ∧ ∀ t, dist (γ i t) c = r) ∧
      Set.InjOn (fun i => ({γ i 0, γ i 1} : Finset ℝ²)) (E : Set ℕ) ∧
      (∀ i ∈ E, ∀ j ∈ E, i ≠ j →
        ((Set.range (γ i) ∩ Set.range (γ j)) \ (A : Set ℝ²)).Finite) ∧
      ((L ×ˢ A).filter fun cp => dist cp.2 cp.1.1 = cp.1.2).card ≤
        2 * E.card + 2 * L.card ∧
      (∑ i ∈ E, ∑ j ∈ E.erase i,
        ((Set.range (γ i) ∩ Set.range (γ j)) \ (A : Set ℝ²)).ncard) ≤
        2 * L.card ^ 2

lemma incidence_of_crossing (K n l e I X : ℕ)
    (hi : I ≤ 2 * e + 2 * l) (hx : X ≤ 2 * l ^ 2)
    (hc : e ≤ K * n ∨ e ^ 3 ≤ K * n ^ 2 * X) :
    I ≤ 128 * (K + 1) * (n + l) ∨
      I ^ 3 ≤ 128 * (K + 1) * n ^ 2 * l ^ 2 := by
  rcases hc with hc | hc
  · left
    nlinarith only [hi, hc]
  · by_cases hl : I ≤ 4 * l
    · left
      nlinarith only [hl]
    · right
      have hie : I ≤ 4 * e := by omega
      calc
        I ^ 3 ≤ (4 * e) ^ 3 := by gcongr
        _ = 64 * e ^ 3 := by ring
        _ ≤ 64 * (K * n ^ 2 * X) := Nat.mul_le_mul_left 64 hc
        _ ≤ 64 * (K * n ^ 2 * (2 * l ^ 2)) := by gcongr
        _ ≤ 128 * (K + 1) * n ^ 2 * l ^ 2 := by nlinarith

theorem main : H1 → H2 → OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1.H1 := by
  rintro ⟨K, hK, hcross⟩ harcs
  refine ⟨128 * (K + 1), by positivity, ?_⟩
  intro A L hpos hmult
  obtain ⟨E, γ, hγ, hinj, hfinite, hi, hx⟩ := harcs A L hpos hmult
  exact incidence_of_crossing K A.card L.card E.card _ _ hi hx
    (hcross A E γ hγ hinj hfinite)

end OMA.R_Erdos604_erdos_604_variants_average_R2_H2_R1_H1_R1
