import OMAReductions.R_erdos_634_R1

/-!
# Erdos 634, reduction R1.H4.R1

Step H4 of R1 (T scalene, some angle of T not a rational multiple of pi, T not similar to the
tile) is split by Laczkovich's classification (1995, Theorem 4.1, with the lemma that T and the
tile are commensurable together): either the tile has angles (α, β, 2α + β) with 3α + 2β = π and
T has angles (α, 2α, 2β) or (2α, β, α + β) (Group 1), or the tile has angles (α, β, 2π/3) with
3α + 3β = π and T has one of four shapes (Group 2), α not a rational multiple of π in both.

* H1: the classification itself.
* H2: Group 2 is impossible for a prime number of tiles.
* H3: Group 1 is impossible for a prime number of tiles (T not similar to the tile).

In each hypothesis A and B are the angle functions of T and of the tile t (A k is the angle at
vertex k).
-/

namespace OMA.R_erdos_634_R1_H4_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ i j, i ≠ j → A i ≠ A j) → ¬ (∀ k, ∃ q : ℚ, A k = q * Real.pi) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) ∧ 3 * α + 2 * β = Real.pi ∧ (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * α + β]) ∧ ∃ σ : Equiv.Perm (Fin 3), A ∘ σ = ![α, 2 * α, 2 * β] ∨ A ∘ σ = ![2 * α, β, α + β]) ∨ (∃ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) ∧ 3 * α + 3 * β = Real.pi ∧ (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * Real.pi / 3]) ∧ ∃ σ : Equiv.Perm (Fin 3), A ∘ σ = ![α, 2 * α, 3 * β] ∨ A ∘ σ = ![α, 2 * β, 2 * α + β] ∨ A ∘ σ = ![α, α + β, α + 2 * β] ∨ A ∘ σ = ![2 * α, 2 * β, α + β])

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∀ k, ∃ q : ℚ, A k = q * Real.pi) → ∀ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 3 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * Real.pi / 3]) → (∃ σ : Equiv.Perm (Fin 3), A ∘ σ = ![α, 2 * α, 3 * β] ∨ A ∘ σ = ![α, 2 * β, 2 * α + β] ∨ A ∘ σ = ![α, α + β, α + 2 * β] ∨ A ∘ σ = ![2 * α, 2 * β, α + β]) → False

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → ∀ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * α + β]) → (∃ σ : Equiv.Perm (Fin 3), A ∘ σ = ![α, 2 * α, 2 * β] ∨ A ∘ σ = ![2 * α, β, α + β]) → False

theorem main : H1 → H2 → H3 → OMA.R_erdos_634_R1.H4 := by
  intro h1 h2 h3 p hp h3p T Ts hc hd hu t hiso hcomm hsim
  have hiso' : ∀ i j : Fin 3, i ≠ j → (fun k => EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) i ≠ (fun k => EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) j :=
    fun i j hij he => hiso ⟨i, j, hij, he⟩
  have hsim' : ¬ (∃ σ : Equiv.Perm (Fin 3), (fun k => EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) = (fun k => EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) ∘ σ) :=
    fun ⟨σ, h⟩ => hsim ⟨σ, fun k => congrFun h k⟩
  rcases h1 p hp h3p T Ts hc hd hu t _ _ (fun k => rfl) (fun k => rfl) hiso' hcomm hsim' with
    ⟨α, β, hα, hr, hB, hA⟩ | ⟨α, β, hα, hr, hB, hA⟩
  · exact h3 p hp h3p T Ts hc hd hu t _ _ (fun k => rfl) (fun k => rfl) hsim' α β hα hr hB hA
  · exact h2 p hp h3p T Ts hc hd hu t _ _ (fun k => rfl) (fun k => rfl) hcomm α β hα hr hB hA

end OMA.R_erdos_634_R1_H4_R1
