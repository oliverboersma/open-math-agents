import OMAReductions.R_erdos_634_R1

/-!
# Erdos 634, step R1.H2 (T isosceles, not similar to the tile), reduction R1

* H1: the repeated angle of T is pi/3 (T equilateral) and some tile angle is not a rational
  multiple of pi.
* H2: Laczkovich's classification of tilings by a tile whose angles are rational multiples of pi:
  T is similar to the tile, or the tile has a right angle and two angles of T equal one of the
  other tile angles (RightRow), or T is equilateral and the tile is (pi/6, pi/6, 2pi/3),
  (pi/12, pi/3, 7pi/12), (pi/30, pi/3, 19pi/30) or (7pi/30, pi/3, 13pi/30).
* H3: the RightRow case is impossible (p prime, p > 3).
* H4: the remaining cases are impossible: T equilateral with one of the four tiles above, or the
  repeated angle of T is not pi/3 and some tile angle is not a rational multiple of pi.
In H2, H3, H4, A and B are the angle functions of T and of the tile t (A k is the angle at
vertex k). The proof of main is a case analysis only.
-/

namespace OMA.R_erdos_634_R1_H2_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2)) ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = Real.pi / 3) → ¬ (∀ k : Fin 3, ∃ q : ℚ, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = q * Real.pi) → ¬ (∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2))) → False

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → (∀ k, ∃ q : ℚ, B k = q * Real.pi) → (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) ∨ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) ∨ ((∀ k, A k = Real.pi / 3) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3] ∨ B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12] ∨ B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30] ∨ B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30])

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) → False

def H4 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ∀ A B : Fin 3 → ℝ, (∀ k, A k = EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) → (∀ k, B k = EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) → ¬ (∃ σ : Equiv.Perm (Fin 3), A = B ∘ σ) → ¬ (∃ k l : Fin 3, l ≠ k ∧ B k = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ A i = B l ∧ A j = B l) → ((∀ k, A k = Real.pi / 3) ∧ ∃ σ : Equiv.Perm (Fin 3), B ∘ σ = ![Real.pi / 6, Real.pi / 6, 2 * Real.pi / 3] ∨ B ∘ σ = ![Real.pi / 12, Real.pi / 3, 7 * Real.pi / 12] ∨ B ∘ σ = ![Real.pi / 30, Real.pi / 3, 19 * Real.pi / 30] ∨ B ∘ σ = ![7 * Real.pi / 30, Real.pi / 3, 13 * Real.pi / 30]) ∨ ((∃ i j : Fin 3, i ≠ j ∧ A i = A j ∧ A i ≠ Real.pi / 3) ∧ ¬ (∀ k, ∃ q : ℚ, B k = q * Real.pi)) → False

theorem main : H1 → H2 → H3 → H4 → OMA.R_erdos_634_R1.H2 := by
  intro g1 g2 g3 g4 p hp hp3 T Ts hc hd hu t hi hs
  have hs' : ¬ (∃ σ : Equiv.Perm (Fin 3), (fun k : Fin 3 => EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2))) = (fun k : Fin 3 => EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2))) ∘ σ) :=
    fun ⟨σ, h⟩ => hs ⟨σ, fun k => congrFun h k⟩
  by_cases hrr : (∃ k l : Fin 3, l ≠ k ∧ EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = Real.pi / 2 ∧ ∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle ((Ts t).points (l + 1)) ((Ts t).points l) ((Ts t).points (l + 2)) ∧ EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2)) = EuclideanGeometry.angle ((Ts t).points (l + 1)) ((Ts t).points l) ((Ts t).points (l + 2)))
  · exact g3 p hp hp3 T Ts hc hd hu t _ _ (fun k => rfl) (fun k => rfl) hs' hrr
  by_cases hr : (∀ k : Fin 3, ∃ q : ℚ, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = q * Real.pi)
  · rcases g2 p hp hp3 T Ts hc hd hu t _ _ (fun k => rfl) (fun k => rfl) hr with h | h | h
    · exact hs' h
    · exact hrr h
    · exact g4 p hp hp3 T Ts hc hd hu t _ _ (fun k => rfl) (fun k => rfl) hs' hrr (Or.inl h)
  · obtain ⟨i, j, hij, he⟩ := hi
    by_cases hθ : EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = Real.pi / 3
    · exact g1 p hp hp3 T Ts hc hd hu t ⟨i, j, hij, he, hθ⟩ hr hs
    · exact g4 p hp hp3 T Ts hc hd hu t _ _ (fun k => rfl) (fun k => rfl) hs' hrr (Or.inr ⟨⟨i, j, hij, he, hθ⟩, hr⟩)

end OMA.R_erdos_634_R1_H2_R1
