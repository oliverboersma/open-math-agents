import OMAReductions.R_erdos_634_R1_H2_R1

/-!
# Erdos 634, reduction R1.H2.R1.H1.R1

T equilateral, the tile t with an angle not a rational multiple of π. By Laczkovich (2012, Thm 3.3 (iv),
(v)) the tile has angles (α, 2π/3 - α, π/3) or (α, π/3 - α, 2π/3), α not in Q π (H1); H2 and H3
exclude a prime number of tiles in the two cases (Beeson-Rosu, theorem:notprime60 and
theorem:notprime120).

In each hypothesis T is the big triangle, Ts the tiles and t a tile; A, B are the angle functions of T
and of the tile t (A k is the angle at vertex k) and L k is the side of the tile t opposite vertex k.
-/

namespace OMA.R_erdos_634_R1_H2_R1_H1_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∃ i j : Fin 3, i ≠ j ∧ A i = A j ∧ A i = Real.pi / 3) → ¬ (∀ k, ∃ q : ℚ, B k = q * Real.pi) → (∀ k, A k = Real.pi / 3) ∧ ((∃ α : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, 2 * Real.pi / 3 - α, Real.pi / 3]) ∨ (∃ α : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3]))

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → ∀ α : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, 2 * Real.pi / 3 - α, Real.pi / 3]) → False

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, A k = Real.pi / 3) → ∀ α : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3]) → False

theorem main : H1 → H2 → H3 → OMA.R_erdos_634_R1_H2_R1.H1 :=
  by
  intro h1 h2 h3 p hp h3p T Ts hc hd hu t hiso hirr _
  obtain ⟨hEq, ⟨α, hα, hB⟩ | ⟨α, hα, hB⟩⟩ :=
    h1 p hp h3p T Ts hc hd hu t _ _ (fun _ => rfl) (fun _ => rfl) hiso hirr
  · exact h2 p hp h3p T Ts hc hd hu t _ _ (fun _ => rfl) (fun _ => rfl) hEq α hα hB
  · exact h3 p hp h3p T Ts hc hd hu t _ _ (fun _ => rfl) (fun _ => rfl) hEq α hα hB

end OMA.R_erdos_634_R1_H2_R1_H1_R1
