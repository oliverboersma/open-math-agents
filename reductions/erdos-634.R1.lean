import OMAStatements.S_erdos_634

/-!
# Erdos 634, reduction R1

Splits the prime case by the shape of the big triangle T relative to a tile: similar (H1),
isosceles (H2), scalene with commensurable angles (H3), scalene with an angle not in Q pi (H4).
-/

namespace OMA.R_erdos_634_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, (∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))) → p % 4 = 1
def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))) → False
def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → (∀ k : Fin 3, ∃ q : ℚ, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2)))
def H4 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ¬ (∀ k : Fin 3, ∃ q : ℚ, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = q * Real.pi) → ¬ (∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))) → False

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_erdos_634.main := by
  intro h1 h2 h3 h4 p hp h43 hgt hcut
  obtain ⟨T, Ts, hc, hd, hu⟩ := hcut
  have t : Fin p := ⟨0, by omega⟩
  by_cases hs : ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))
  · have := h1 p hp hgt T Ts hc hd hu t hs
    omega
  by_cases hi : ∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))
  · exact h2 p hp hgt T Ts hc hd hu t hi hs
  by_cases hm : ∀ k : Fin 3, ∃ q : ℚ, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = q * Real.pi
  · exact hs (h3 p hp hgt T Ts hc hd hu t hi hm)
  · exact h4 p hp hgt T Ts hc hd hu t hi hm hs

end OMA.R_erdos_634_R1
