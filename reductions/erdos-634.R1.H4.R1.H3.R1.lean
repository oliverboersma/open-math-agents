import OMAReductions.R_erdos_634_R1_H4_R1

/-!
# Erdos 634, reduction R1.H4.R1.H3.R1

Group 1 (tile (α, β, 2α + β), 3α + 2β = π, α not in Q pi, T with angles (α, 2α, 2β) or
(2α, β, α + β)) is excluded given two facts about any tiling by such a tile (H1):
* the tile is rational (its sides are commensurable) when T is not similar to it
  (Beeson-Rosu, theorem:rationaltile);
* the j = 1 case of theorem:triquadratic: if T has angles (2α, β, α + β) at its vertices 0, 1, 2
  and the sides of the tile are (mk, k^2 - m^2, k^2) with 0 < m < k coprime, then the number of
  tiles is not 2k^2 - m^2.
H2 is the rest of the Group 1 argument (TriangleTiling3 Theorem 16 for (α, 2α, 2β), and
theorem:triquadratic for (2α, β, α + β)) given H1.

In H1, the tiling is given by cut data T, Ts and a model triangle M: each tile is the image of M
under an isometry of the plane, up to relabelling the vertices; A, B are the angle functions of T
and M, L k the side of M opposite vertex k.
-/

namespace OMA.R_erdos_634_R1_H4_R1_H3_R1

def H1 : Prop := ∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α β γ a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, γ] ∧ L ∘ σ = ![a, b, c]) → (¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)) ∧ ∀ m k : ℤ, 0 < m → m < k → IsCoprime m k → a = m * k → b = k ^ 2 - m ^ 2 → c = k ^ 2 → A = ![2 * α, β, α + β] → (p : ℝ) ≠ 2 * k ^ 2 - m ^ 2

def H2 : Prop := (∀ (p : ℕ) (T M : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i, ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (σ : Equiv.Perm (Fin 3)), ∀ k, f ((Ts i).points k) = M.points (σ k)) → Pairwise (fun i j => Disjoint (interior (Ts i).closedInterior) (interior (Ts j).closedInterior)) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ A B L : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle (M.points (k + 1)) (M.points k) (M.points (k + 2))) → (∀ k, L k = dist (M.points (k + 1)) (M.points (k + 2))) → ∀ α β γ a b c : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, γ] ∧ L ∘ σ = ![a, b, c]) → (¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)) ∧ ∀ m k : ℤ, 0 < m → m < k → IsCoprime m k → a = m * k → b = k ^ 2 - m ^ 2 → c = k ^ 2 → A = ![2 * α, β, α + β] → (p : ℝ) ≠ 2 * k ^ 2 - m ^ 2) → ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → ∀ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * α + β]) → (∃ σ : Equiv.Perm (Fin 3), A ∘ σ = ![α, 2 * α, 2 * β] ∨ A ∘ σ = ![2 * α, β, α + β]) → False

theorem main : H1 → H2 → OMA.R_erdos_634_R1_H4_R1.H3 := fun h1 h2 => h2 h1

end OMA.R_erdos_634_R1_H4_R1_H3_R1
