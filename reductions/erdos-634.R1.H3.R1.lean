import OMAReductions.R_erdos_634_R1

/-!
# Erdos 634, reduction erdos-634.R1.H3.R1

Scalene big triangle with all angles rational multiples of pi. H1: the tile angles are then
a k * pi / n with n > 0 and gcd (a 0, a 1, a 2) = 1. H2, H3, H4: the big triangle is similar to the
tile, according to the prime factors of n (some prime at least 7; all primes at most 5 and n > 200;
all primes at most 5 and n at most 200).
-/

namespace OMA.R_erdos_634_R1_H3_R1

def H1 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → (∀ k : Fin 3, ∃ q : ℚ, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = q * Real.pi) → ∃ (n : ℕ) (a : Fin 3 → ℕ), 0 < n ∧ (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) ∧ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1

def H2 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), 0 < n → (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ l ∣ n) → (∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2)))

def H3 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), 0 < n → (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5) → 200 < n → (∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2)))

def H4 : Prop := ∀ (p : ℕ), p.Prime → 3 < p → ∀ (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (Ts : Fin p → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))), (∀ i j, Congruent (Ts i).points (Ts j).points) → Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) → ⋃ i, (Ts i).closedInterior = T.closedInterior → ∀ t : Fin p, ¬ (∃ i j : Fin 3, i ≠ j ∧ EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2)) = EuclideanGeometry.angle (T.points (j + 1)) (T.points j) (T.points (j + 2))) → ∀ (n : ℕ) (a : Fin 3 → ℕ), 0 < n → (∀ k : Fin 3, EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) = (a k : ℝ) * Real.pi / n) → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5) → n ≤ 200 → (∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3, EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) = EuclideanGeometry.angle ((Ts t).points ((σ k) + 1)) ((Ts t).points (σ k)) ((Ts t).points ((σ k) + 2)))

theorem main : H1 → H2 → H3 → H4 → OMA.R_erdos_634_R1.H3 := by
  intro h1 h2 h3 h4 p hp hgt T Ts hc hd hu t hi hm
  obtain ⟨n, a, hn, ha, hg⟩ := h1 p hp hgt T Ts hc hd hu t hi hm
  by_cases hs : ∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5
  · by_cases h200 : n ≤ 200
    · exact h4 p hp hgt T Ts hc hd hu t hi n a hn ha hg hs h200
    · exact h3 p hp hgt T Ts hc hd hu t hi n a hn ha hg hs (by omega)
  · push Not at hs
    obtain ⟨l, hl, hln, h5⟩ := hs
    refine h2 p hp hgt T Ts hc hd hu t hi n a hn ha hg ⟨l, hl, ?_, hln⟩
    by_contra h7
    have h6 : l = 6 := by omega
    subst h6
    exact absurd hl (by norm_num)

end OMA.R_erdos_634_R1_H3_R1
