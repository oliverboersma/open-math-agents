import OMAReductions.R_erdos_634_R1_H2_R1

/-!
# Erdos 634, reduction R1.H2.R1.H4.R1

The remaining isosceles cases (T not similar to the tile, not the RightRow case):
* H1: T equilateral and the tile is (pi/6, pi/6, 2pi/3), (pi/12, pi/3, 7pi/12),
  (pi/30, pi/3, 19pi/30) or (7pi/30, pi/3, 13pi/30): impossible.
* H2: Laczkovich's classification for an isosceles T whose repeated angle θ is not pi/3 and a
  tile with an angle not in Q pi (Beeson-Rosu, cor:isoprime): the tile is (θ, pi - 3θ, 2θ) with θ
  not in Q pi, or (α, β, 2α + β) with 3α + 2β = pi, α not in Q pi and θ one of α, β, α + β.
* H3: the tile (θ, pi - 3θ, 2θ) is impossible (theorem:notsquarefree).
* H4: the tile (α, β, 2α + β) is impossible (theorem:notprime3, notprime5, isoscelesbeta).
A and B are the angle functions of T and of the tile t (A k is the angle at vertex k).
-/

namespace OMA.R_erdos_634_R1_H2_R1_H4_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∀ k, A k = Real.pi / 3) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3] ∨ B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12] ∨ B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30] ∨ B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30]) → False

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → ¬ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) → (∃ i j : Fin 3, i ≠ j ∧ A i = A j ∧ A i ≠ Real.pi / 3) → ¬ (∀ k, ∃ q : ℚ, B k = q * Real.pi) → (∃ i j : Fin 3, i ≠ j ∧ A i = A j ∧ (¬ ∃ q : ℚ, A i = q * Real.pi) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![A i, Real.pi - 3 * A i, 2 * A i]) ∨ (∃ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) ∧ 3 * α + 2 * β = Real.pi ∧ (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * α + β]) ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = A j ∧ (A i = α ∨ A i = β ∨ A i = α + β))

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ∀ i j : Fin 3, i ≠ j → A i = A j → (¬ ∃ q : ℚ, A i = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![A i, Real.pi - 3 * A i, 2 * A i]) → False

def H4 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → ∀ α β : ℝ, (¬ ∃ q : ℚ, α = q * Real.pi) → 3 * α + 2 * β = Real.pi → (∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![α, β, 2 * α + β]) → ∀ i j : Fin 3, i ≠ j → A i = A j → (A i = α ∨ A i = β ∨ A i = α + β) → False

theorem main : H1 → H2 → H3 → H4 → OMA.R_erdos_634_R1_H2_R1.H4 := by
  intro g1 g2 g3 g4 p hp hp3 T Ts hc hd hu t A B hA hB hs hrr hcase
  rcases hcase with ⟨heq, hsh⟩ | ⟨hiso, hirr⟩
  · exact g1 p hp hp3 T Ts hc hd hu t A B hA hB hs heq hsh
  · rcases g2 p hp hp3 T Ts hc hd hu t A B hA hB hs hrr hiso hirr with
      ⟨i, j, hij, he, hi, hσ⟩ | ⟨α, β, hα, hrel, hσ, i, j, hij, he, hθ⟩
    · exact g3 p hp hp3 T Ts hc hd hu t A B hA hB i j hij he hi hσ
    · exact g4 p hp hp3 T Ts hc hd hu t A B hA hB hs α β hα hrel hσ i j hij he hθ

end OMA.R_erdos_634_R1_H2_R1_H4_R1
