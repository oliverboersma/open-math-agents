import OMAReductions.R_erdos_634_R1_H4_R1

/-!
# Erdos 634, reduction R1.H4.R1.H2.R1

Group 2 (tile (α, β, 2π/3), 3α + 3β = π, α not in Q pi) is excluded through the theorem of
Beeson and Zhang (Theorem 1.1): if a triangle not similar to the tile is tiled by a tile with
angles (α, π/3 - α, 2π/3), α not a rational multiple of π, then the sides a, b, c of the tile are
commensurable. H1 is that theorem, H2 the rest of the Group 2 argument (Beeson-Rosu,
theorem:case2 to theorem:case5) given H1.

In H1, the tiling is given by cut data T, Ts and a model triangle M: each tile is the image of M
under an isometry of the plane, up to relabelling the vertices; A, B are the angle functions of T
and M, L k the side of M opposite vertex k.
-/

namespace OMA.R_erdos_634_R1_H4_R1_H2_R1

def H1 : Prop := ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)

def H2 : Prop := (∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, Real.pi / 3 - α, 2 * Real.pi / 3] ∧ L ∘ σ = ![a, b, c]) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * b) ∧ (∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * a = n * c)) → ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∀ k, ∃ q : ℚ, A k = q * Real.pi) → ∀ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 3 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * Real.pi / 3]) → (∃ σ : Equiv.Perm (Fin 3), A ∘ σ = ![α, 2 * α, 3 * β] ∨ A ∘ σ = ![α, 2 * β, 2 * α + β] ∨ A ∘ σ = ![α, α + β, α + 2 * β] ∨ A ∘ σ = ![2 * α, 2 * β, α + β]) → False

theorem main : H1 → H2 → OMA.R_erdos_634_R1_H4_R1.H2 := fun h1 h2 => h2 h1

end OMA.R_erdos_634_R1_H4_R1_H2_R1
